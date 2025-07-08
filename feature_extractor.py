import pandas as pd
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
from urllib.parse import urlparse, parse_qs
from rich.progress import (
    Progress,
    BarColumn,
    TextColumn,
    TimeElapsedColumn,
    TimeRemainingColumn,
    MofNCompleteColumn
)
from datetime import datetime
import random
from copy import deepcopy
import socket
import dns.resolver
import whois
import time
import requests
import ssl
from ipwhois import IPWhois
import re
import os
from functools import lru_cache
from typing import Dict, Any, Optional, List
import logging
import threading

#Enhanced logging configuration
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('execution.log'),  # All logs go here
        logging.StreamHandler()               # Also show in console
    ]
)
logger = logging.getLogger(__name__)

def save_partial_results(results: list, output_path: str):
    """Thread-safe saving with feature validation"""
    if not results:
        logger.warning("No results to save")
        return
        
    try:
        # Validate all records have same features
        expected_keys = set(results[0].keys())
        for i, record in enumerate(results[1:]):
            if set(record.keys()) != expected_keys:
                logger.error(f"Feature mismatch at index {i+1}:")
                logger.error(f"Expected keys: {expected_keys}")
                logger.error(f"Found keys: {set(record.keys())}")
                raise ValueError("Inconsistent feature sets detected")

        df = pd.DataFrame(results)
        
        # Convert labels if column exists
        if 'phishing' in df.columns:
            df['phishing'] = df['phishing'].apply(
                lambda x: 1 if str(x).strip().lower() == 'phishing' else 0
            )
        
        # Merge with existing results
        if os.path.exists(output_path):
            existing = pd.read_csv(output_path)
            df = pd.concat([existing, df]).drop_duplicates('url', keep='last')
        
        # Save all features
        df.to_csv(output_path, index=False)
        logger.info(f"Saved {len(df)} records with {len(df.columns)} features to {output_path}")
        
    except Exception as e:
        logger.error(f"Save failed: {str(e)}", exc_info=True)

# Constants
DEFAULT_TIMEOUT = 8

SHORTENERS = [
    'bit.ly', 'tinyurl.com', 'goo.gl', 't.co', 'ow.ly', 'buff.ly', 'is.gd',
    'tr.im', 'cli.gs', 'yfrog.com', 'migre.me', 'ff.im', 'tiny.cc', 'url4.eu',
    'twit.ac', 'su.pr', 'twurl.nl', 'snipurl.com', 'short.to', 'BudURL.com',
    'ping.fm', 'post.ly', 'Just.as', 'bkite.com', 'snipr.com', 'fic.kr', 'loopt.us',
    'doiop.com', 'short.ie', 'kl.am', 'wp.me', 'rubyurl.com', 'om.ly', 'to.ly',
    'bit.do', 'lnkd.in', 'db.tt', 'qr.ae', 'adf.ly', 'bitly.com', 'cur.lv', 'u.to',
    'j.mp', 'buzurl.com', 'cutt.us', 'u.bb', 'yourls.org', 'scrnch.me', 'qr.net'
]
TLDS = ['.com', '.net', '.org', '.edu', '.gov', '.uk', '.de', '.jp', '.fr', 
        '.au', '.us', '.ru', '.ch', '.it', '.nl', '.se', '.no', '.es', '.mil']
VOWELS = 'aeiouAEIOU'
IP_PATTERN = r'^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$'

SPECIAL_CHARS = ['dot', 'hyphen', 'underline', 'slash', 'questionmark', 'equal',
                 'at', 'and', 'exclamation', 'space', 'tilde', 'comma', 'plus',
                 'asterisk', 'hashtag', 'dollar', 'percent']
user_agents = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:89.0) Gecko/20100101 Firefox/89.0',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/88.0.4324.182 Safari/537.36',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 14_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0 Mobile/15E148 Safari/604.1'
]

progress_columns = [
    TextColumn("[progress.description]{task.description}"),
    BarColumn(),
    MofNCompleteColumn(),
    TextColumn("•"),
    TimeElapsedColumn(),
    TextColumn("•"),
    TimeRemainingColumn(),
]

class FeatureExtractor:
    def __init__(self):
        self._session = None
        self._session_lock = threading.Lock()
        
    @property
    def session(self):
        if self._session is None:
            with self._session_lock:
                if self._session is None:
                    self._session = requests.Session()
                    self._session.headers.update({'User-Agent': 'Mozilla/5.0'})
        return self._session
    
    def _count_special_chars(self, text: str, prefix: str) -> Dict[str, int]:
        """Precise special character counting per table specs"""
        char_map = {
            'dot': '.',
            'hyphen': '-',
            'underline': '_',
            'slash': '/',
            'questionmark': '?',
            'equal': '=',
            'at': '@',
            'and': '&',
            'exclamation': '!',
            'space': ' ',
            'tilde': '~',
            'comma': ',',
            'plus': '+',
            'asterisk': '*',
            'hashtag': '#',
            'dollar': '$',
            'percent': '%'
    }
        return {f'qty_{char}_{prefix}': text.count(symbol) for char, symbol in char_map.items()}
    
    def _extract_basic_features(self, url: str) -> Dict[str, Any]:
        """Whole URL features (20)"""
        features = {
            'url': url,
            'length_url': len(url),
            'email_in_url': int(bool(re.search(r'\b[\w.-]+?@\w+?\.\w+?\b', url))),
            'url_shortened': int(any(s in url for s in SHORTENERS))           
        }
        # Add TLD count feature (qty_tld_url)
        parsed_url = urlparse(url)
        domain_parts = parsed_url.netloc.split('.')
        features['qty_tld_url'] = len(domain_parts[-1].split('.')) if domain_parts else 0
        # Add parameter count feature (qty_params)
        features['qty_params'] = len(parse_qs(parsed_url.query))

        features.update(self._count_special_chars(url, 'url'))

        return features
    
    def _extract_domain_features(self, domain: str) -> Dict[str, Any]:
        """Domain features (21)"""
        if not domain:
            return {f'qty_{char}_domain': -1 for char in SPECIAL_CHARS} | {
                'domain_length': -1,
                'domain_in_ip': -1,
                'server_client_domain': -1
            }
        
        features = {
            'domain_length': len(domain),
            'domain_in_ip': int(bool(re.fullmatch(IP_PATTERN, domain))),
            'server_client_domain': int(('server' in domain.lower() or 'client' in domain.lower())),
            'qty_vowels_domain': sum(1 for char in domain if char.lower() in VOWELS)
        }
        features.update(self._count_special_chars(domain, 'domain'))
        return features
    
    def _extract_directory_features(self, path: str) -> Dict[str, Any]:
        """Extracts 18 directory-related features from URL path"""
        if not path:
            return {f'qty_{char}_directory': -1 for char in SPECIAL_CHARS} | {
                'directory_length': -1,
                'qty_directories': -1
            }
        
        # Split path into components and exclude filename (parts containing dots)
        directories = [part for part in path.split('/') if part and '.' not in part]
        dir_path = '/'.join(directories)  # Combined directory path
        
        features = {
            'directory_length': len(dir_path),
            'qty_directories': len(directories),
        }
        features.update(self._count_special_chars(dir_path, 'directory'))
        return features
        
    def _extract_file_features(self, path: str) -> Dict[str, Any]:
        """Extracts 18 file-related features from URL path"""
        if not path:
            return {f'qty_{char}_file': -1 for char in SPECIAL_CHARS} | {
                'file_length': -1
            }
        
        # Extract filename (last component containing a dot)
        filename = next((part for part in reversed(path.split('/')) 
                    if part and '.' in part), '')
        
        features = {
            'file_length': len(filename),
        }
        features.update(self._count_special_chars(filename, 'file'))
        return features

    def _extract_params_features(self, params: str) -> Dict[str, Any]:
        """Parameter features (20)"""
        if not params:
            return {f'qty_{char}_params': -1 for char in SPECIAL_CHARS} | {
                'params_length': -1,
                'tld_present_params': -1,
                'qty_params': -1
            }
        
        features = {
            'params_length': len(params),
            'tld_present_params': int(any(tld in params.lower() for tld in TLDS)),
            'qty_params': len(parse_qs(params))
        }
        features.update(self._count_special_chars(params, 'params'))
        return features
    
    @lru_cache(maxsize=1024)
    def _get_dns_info(self, domain: str, record_type: str) -> Optional[list]:
        """Cached DNS resolver with proper error handling"""
        try:
            answers = dns.resolver.resolve(domain, record_type, lifetime=DEFAULT_TIMEOUT)
            return [r.to_text() for r in answers]
        except dns.resolver.NXDOMAIN:
            logger.debug(f"DNS record not found for {domain} {record_type}")
            return None
        except dns.resolver.NoAnswer:
            logger.debug(f"No DNS answer for {domain} {record_type}")
            return None
        except dns.resolver.Timeout:
            logger.debug(f"DNS timeout for {domain} {record_type}")
            return None
        except Exception as e:
            logger.debug(f"DNS lookup failed for {domain} {record_type}: {str(e)}")
            return None
    
    @lru_cache(maxsize=1024)
    def _get_whois_info(self, domain: str) -> Optional[dict]:
        """Cached WHOIS lookup with proper error handling"""
        try:
            info = whois.whois(domain)
            return info if isinstance(info, dict) else None
        except whois.parser.PywhoisError:
            logger.debug(f"WHOIS lookup failed for {domain}")
            return None
        except Exception as e:
            logger.debug(f"WHOIS exception for {domain}: {str(e)}")
            return None
    
    def _extract_external_features(self, url: str, domain: str) -> Dict[str, Any]:
        """Extract features requiring external requests."""
        features = {}
        
        # HTTP Time Response
        try:
            start = time.time()
            response = self.session.head(url, timeout=DEFAULT_TIMEOUT, allow_redirects=True)
            features['time_response'] = round (time.time() - start , 8)
            features['qty_redirects'] = len(response.history)
        except Exception as e:
            features['time_response'] = -1
            features['qty_redirects'] = -1
            logger.debug(f"HTTP request failed for {url}: {str(e)}")
        
        # DNS resolution
        try:
            _, _, ip_list = socket.gethostbyname_ex(domain)
            features['qty_ip_resolved'] = len(ip_list)
        except Exception as e:
            features['qty_ip_resolved'] = -1
            logger.debug(f"DNS resolution failed for {domain}: {str(e)}")
        
        # SPF Record
        try:
            spf_records = self._get_dns_info(domain, 'TXT')
            features['domain_spf'] = 1 if spf_records and any('v=spf1' in r for r in spf_records) else 0
        except Exception as e:
            features['domain_spf'] = -1
            logger.debug(f"SPF records lookup failed for {domain}: {str(e)}")
        
        # ASN from IP
        try:
            ip = socket.gethostbyname(domain)
            obj = IPWhois(ip)
            results = obj.lookup_rdap()
            features['asn_ip'] = int(results.get('asn', '').split(' ')[0]) if results.get('asn') else -1
        except Exception as e:
            features['asn_ip'] = -1
            logger.debug(f"ASN lookup failed for {domain}: {str(e)}")
        
        # Domain Activation & Expiration
        # Domain Activation & Expiration
        try:
            parsed_url = urlparse(url)
            domain = parsed_url.hostname
            if not domain:
                features['time_domain_activation'] = -1 # Invalid URL
                features['time_domain_expiration'] = -1 # Invalid URL     
            w = whois.whois(domain)
            # Handle creation_date
            creation_date = w.creation_date
            if isinstance(creation_date, list):
                creation_date = creation_date[0]
            # Handle expiration_date
            expiration_date = w.expiration_date
            if isinstance(expiration_date, list):
                expiration_date = expiration_date[0]
            # Calculate activation and expiration times
            if creation_date and expiration_date:
                activation_days = (datetime.utcnow() - creation_date).days
                expiration_days = (expiration_date - datetime.utcnow()).days
                features['time_domain_activation'] = activation_days
                features['time_domain_expiration'] = expiration_days
        except Exception as e:
            logger.debug(f"Error retrieving WHOIS data for {domain}: {str(e)}")
            features['time_domain_activation'] = -1 # Invalid URL
            features['time_domain_expiration'] = -1 # Invalid URL

        # DNS Features
        try:
            ns_records = self._get_dns_info(domain, 'NS')
            features['qty_nameservers'] = len(ns_records) if ns_records else -1
            mx_records = self._get_dns_info(domain, 'MX')
            features['qty_mx_servers'] = len(mx_records) if mx_records else -1
        except Exception as e:
            features['qty_nameservers'] = -1
            features['qty_mx_servers'] = -1
            logger.debug(f"MX_Nameservers failed for {domain}: {str(e)}")

        #TTL_Hostname
        try:
            parsed_url = urlparse(url)
            domain = parsed_url.hostname
            if not domain:
                features['ttl_hostname'] = -1 # Invalid URL                
            #Initiatiate resolver  
            resolver = dns.resolver.Resolver()
            resolver.nameservers = ['8.8.8.8']  # Use Google's public DNS server
            answers = resolver.resolve(domain, 'A')
            features['ttl_hostname'] = answers.rrset.ttl
        except Exception as e:
            logger.debug(f"Error retrieving TTL Hostname for {domain}: {str(e)}")
            features['ttl_hostname']= -1
        
        # TLS/SSL Certificate
        try:
            # Extract domain from URL
            parsed_url = urlparse(url)
            domain = parsed_url.hostname
            if not domain:
                features['tls_ssl_certificate'] = -1 # Invalid URL

            # Set up SSL context
            context = ssl.create_default_context()
            with socket.create_connection((domain, 443), timeout=DEFAULT_TIMEOUT) as sock:
                with context.wrap_socket(sock, server_hostname=domain) as ssock:
                    ssock.getpeercert()
                    features['tls_ssl_certificate'] = 1  # Valid certificate
        except ssl.SSLError:
            logger.debug(f"Invalid SSL Certicate for {domain}: {str(ssl.SSLError)}")
            features['tls_ssl_certificate'] = 0  # Invalid certificate
        except Exception as e:
            logger.debug(f"SSL Validation Interrupted for {domain}: {str(e)}")
            features['tls_ssl_certificate'] = -1  # Error occurred

        #URL Indexed on Google 
        try:
            response = requests.get(f"https://www.google.com/search?q=site:{url}", headers={'User-Agent': random.choice(user_agents)})
            features['url_google_index'] = 1 if "did not match any documents" not in response.text else 0
         
        except Exception as e:
            logger.debug(f"Google URL indexing failed for {url}: {str(e)}")
            features['url_google_index'] = -1
        
        #Domain Indexed on Google 
        try:
            # Extract domain from URL
            parsed_url = urlparse(url)
            domain = parsed_url.hostname
            if not domain:
                features['domain_google_index'] = -1 # Invalid URL

            response = requests.get(f"https://www.google.com/search?q=site:{domain}", headers = {'User-Agent': random.choice(user_agents)})
            features['domain_google_index'] = 1 if "did not match any documents" not in response.text else 0
         
        except Exception as e:
            logger.debug(f"Google URL indexing failed for {domain}: {str(e)}")
            features['domain_google_index'] = -1

        return features

    def extract_features(self, url: str) -> Dict[str, Any]:
        """Main method now returns exactly 112 features"""
        try:
            parsed = urlparse(url)
            if not parsed.netloc:
                return {'url': url, 'error': 'invalid_url'}
            
            features = {}
            
            # 1. Whole URL (20 features)
            features.update(self._extract_basic_features(url))
            
            # 2. Domain (21 features)
            features.update(self._extract_domain_features(parsed.netloc))
            
            # 3-4. Path components (36 features)
            path = parsed.path
            features.update(self._extract_directory_features(path))  # 18 features
            features.update(self._extract_file_features(path))      # 18 features

            # 5. Parameters (20 features)
            features.update(self._extract_params_features(parsed.query))
            
            # 6. External (15 features)
            external = self._extract_external_features(url, parsed.netloc)
            external.pop('phishing', None)  # Remove if present
            features.update(external)
            
            return features
            
        except Exception as e:
            logger.error(f"Error processing {url}: {str(e)}")
            return {'url': url, 'error': str(e)}
    
#Global lock for thread-safe append
lock = Lock()

def process_url(url: str, label: str, results: list):
    """Process URL with thread-safe feature preservation"""
    extractor = FeatureExtractor()
    try:
        features = extractor.extract_features(url)
        if 'error' in features:
            logger.warning(f"Skipping malformed URL: {url}")
            return
            
        features['phishing'] = label
        with lock:
            results.append(deepcopy(features))  # Critical: deepcopy for thread safety
            
    except Exception as e:
        logger.error(f"Failed to process {url}: {str(e)}")

def main(input_csv: str, output_csv: str):
    """Main processing with enhanced thread safety"""
    try:
        # Load data
        df = pd.read_csv(input_csv)
        if os.getenv('DEBUG'):
            df = df.head(50)
            logger.info("DEBUG mode - processing first 50 URLs")
        
        # Verify columns
        if 'url' not in df.columns:
            raise ValueError("Input CSV must contain 'url' column")
        
        label_col = 'phishing' if 'phishing' in df.columns else df.columns[-1]
        logger.info(f"Using '{label_col}' as label column")
        
        # Initialize
        results = []
        processed_urls = set()
        
        # Resume functionality
        if os.path.exists(output_csv):
            try:
                existing = pd.read_csv(output_path)
                processed_urls = set(existing['url'].tolist())
                logger.info(f"Resuming with {len(processed_urls)} existing records")
            except:
                logger.warning("Couldn't read existing output file")
        
        # Process URLs
        with Progress(*progress_columns) as progress:
            task = progress.add_task("[cyan]Processing...", total=len(df))
            
            with ThreadPoolExecutor(max_workers=4) as executor:
                futures = []
                for _, row in df.iterrows():
                    url = str(row['url']).strip()
                    label = str(row[label_col]).strip()
                    
                    if not url or url in processed_urls:
                        progress.update(task, advance=1)
                        continue
                        
                    futures.append(executor.submit(process_url, url, label, results))
                
                try:
                    for future in as_completed(futures):
                        try:
                            future.result()
                            if len(results) % 1000 == 0:
                                save_partial_results(results, output_csv)
                        except Exception as e:
                            logger.error(f"Processing error: {str(e)}")
                        finally:
                            progress.update(task, advance=1)
                except KeyboardInterrupt:
                    logger.info("Interrupt received - saving partial results")
        
        # Final save
        save_partial_results(results, output_csv)
        
    except Exception as e:
        logger.error(f"Fatal error: {str(e)}", exc_info=True)

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("input_csv", help="Input CSV with URLs")
    parser.add_argument("output_csv", help="Output CSV for features")
    args = parser.parse_args()
    
    # Convert to absolute paths
    input_path = os.path.abspath(args.input_csv)
    output_path = os.path.abspath(args.output_csv)
    
    main(input_path, output_path)

"""
help:
        python feature_extractor.py [-h]
output:
        usage: feature_extractor.py [-h] input_csv output_csv

        positional arguments:
        input_csv   Input CSV with URLs
        output_csv  Output CSV for features

        optional arguments:
        -h, --help  show this help message and exit

USAGE COMMAND: 

            python feature_extractor [input.csv] [output.csv]

            To run on actual dataset:
                python feature_extractor.py input.csv output_features.csv
            To run in DEBUG mode. DEBUG MODE = first 100 URL (Adjustable from code) instances from Dataset
                DEBUG=1 python feature_extractor.py preprocessed.csv features.csv
            All logs are kept in execution.log, this is good for error tracing and safe resumption interrupted extraction process

            GOOD LUCK!!!
    
"""