import subprocess
import os
import glob
import json
import re
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
    print("Folder:")
    print(FOLDER)

    failed = False
    print("Current working directory:")
    print(os.getcwd())
    print("fcc version:")
    result = subprocess.run(['which', 'fcc'], capture_output=True)
    print(result.stdout)
    if not os.path.isdir(FOLDER):
        raise Exception(f"Could not find the folder {FOLDER}")
    for filename in glob.iglob('**/*.mv', recursive=True, root_dir=FOLDER):
        if filename.endswith('notest.mv'):
            print(f"Skipping {filename} as it is a notest file")
            continue
        print(filename)
        result = subprocess.run(['fcc', '--root=../../../', f'{FOLDER}/{filename}'],
                       capture_output=True)
        if result.returncode != 0:
            raise Exception(f"Compilation of file {filename} has failed\n{result.stderr}")
    for filename in glob.iglob('**/*.diags', recursive=True, root_dir=FOLDER):
        print(filename)
        with open(f'{FOLDER}/{filename}') as file:
            # Load optional .test file (same name but .test instead of .diags).
            diags_path = os.path.join(FOLDER, filename)
            test_path = os.path.splitext(diags_path)[0] + '.test'
            lemmas = set()
            if os.path.exists(test_path):
                with open(test_path) as tf:
                    for line in tf:
                        line = line.strip()
                        if not line or line.startswith('#'):
                            continue
                        lemmas.add(line)

            contents = file.read().replace('}\n{','},{')
            diags = json.loads('[' + contents + ']')
            for diag in diags:
                sev = diag.get('severity', 0)
                if sev <= 1:
                    # Check if message has proof name that is expected to fail
                    msg = diag.get('message')

                    # Extract lemma names from patterns like "(in proof <lemma>)"
                    proof_lemmas = re.findall(r"\(in proof\s+([^\)]+)\)", msg)

                    skip = False
                    for pl in proof_lemmas:
                        pl = pl.strip()
                        if pl in lemmas:
                            skip = True
                            break
                    if skip:
                        continue

                    print(filename)
                    print(diag)
                    failed = True
    if failed:
        raise Exception("The tests against the exercises have failed")
