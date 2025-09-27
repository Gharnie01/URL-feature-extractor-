# URL-feature-extractor
A malleable python script for URL feature extraction for machine learning and deep learning research and projects.

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
    
