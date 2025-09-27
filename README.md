# URL-feature-extractor
A malleable python script for URL feature extraction for machine learning and deep learning research and projects.

<img width="1689" height="440" alt="image" src="https://github.com/user-attachments/assets/42350178-aa52-4d26-bfd5-90f0e64c76d5" />

Resume from an unfinished extraction

<img width="1856" height="789" alt="image" src="https://github.com/user-attachments/assets/c0185c30-a868-457b-bde2-615dd316f656" />

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
    
