import subprocess
import os
import glob
import json

if __name__ == "__main__":
    failed = False
    print("Current working directory:")
    print(os.getcwd())
    for filename in glob.iglob('**/*.mv', recursive=True, root_dir="../../../../waterproof-exercises"):
        subprocess.run(['fcc', '--root=../../../', f'../../../../waterproof-exercises/{filename}'])
    for filename in glob.iglob('**/*.diags', recursive=True, root_dir="../../../../waterproof-exercises"):
        with open(f'../../../../waterproof-exercises/{filename}') as file:
            contents = file.read().replace('}\n{','},{')
            diags = json.loads('[' + contents + ']')
            for diag in diags:
                if(diag['severity'] <= 1):
                    print(filename)
                    print(diag)
                    failed = True
    if failed:
        raise Exception("The tests against the exercises have failed")
