import subprocess
import os
import glob
import json
import argparse

if __name__ == "__main__":
    PARSER = argparse.ArgumentParser(
        description='Test all mv files in a directory recursively against the current library.')
    PARSER.add_argument('folder', type=str,
                        help='The directory to test')
    PARSER.add_argument('--exclude', type=str,
                        help='(Not implemented) file pattern to exclude')

    ARGS = PARSER.parse_args()
    FOLDER = ARGS.folder
    EXCLUDE = ARGS.exclude

    print(FOLDER)

    failed = False
    print("Current working directory:")
    print(os.getcwd())
    for filename in glob.iglob('**/*.mv', recursive=True, root_dir=FOLDER):
        print(filename)
        result = subprocess.run(['fcc', '--root=../../../', f'{FOLDER}/{filename}'],
                       capture_output=True)
        if result.returncode != 0:
            raise Exception(f"Compilation of file {filename} has failed\n{result.stderr}")
    for filename in glob.iglob('**/*.diags', recursive=True, root_dir=FOLDER):
        print(filename)
        with open(f'{FOLDER}/{filename}') as file:
            contents = file.read().replace('}\n{','},{')
            diags = json.loads('[' + contents + ']')
            for diag in diags:
                if(diag['severity'] <= 1):
                    print(filename)
                    print(diag)
                    failed = True
    if failed:
        raise Exception("The tests against the exercises have failed")
