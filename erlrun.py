import subprocess
import sys

def execute_machines(name):
    subprocess.run(f'erl -eval "{name}:main()" -s init stop',
        cwd=f'{name}',
        shell=True)
    subprocess.run(f'erlc {name}_{name}.erl',
        cwd=f'{name}',
        shell=True)
    subprocess.run(f'erl -eval "{name}_{name}:main()" -s init stop',
        cwd=f'{name}',
        shell=True)

if __name__ == "__main__":
    """
    Executes the generated Erlang code in a loop.
    Assumes CWD to be correctly set. 
    First param is the name of the thing to run.
    """
    if len(sys.argv) > 1:
        name = sys.argv[1]
        while True:
            execute_machines(name)
    else:
        print('Filename needed')

        