# %%
import subprocess

import time
import os
from pathlib import Path
from subprocess import Popen, DEVNULL, PIPE, TimeoutExpired

def add_bitwuzla_at(path):
    os.environ['BITWUZLA_PATH'] = path

# %%

TIME_LIMIT_SECONDS = 60
REPO_PATH = Path(__file__).parent.parent
SOLVER_PATH = REPO_PATH / 'target' / 'release' / 'egraph-smt-bv'
# Must be in path
SOLVER_CMDLINES = [[str(SOLVER_PATH), '<INPUT>', '-t', str(TIME_LIMIT_SECONDS * 1000)], ['z3', f'-T:{TIME_LIMIT_SECONDS}', '<INPUT>']]

if 'BITWUZLA_PATH' in os.environ:
    SOLVER_CMDLINES.append([os.environ['BITWUZLA_PATH'], '-t', str(TIME_LIMIT_SECONDS), '<INPUT>'])

print(SOLVER_CMDLINES)

REPO_PATH, SOLVER_CMDLINES

# %%

# Making sure that solver's binary is up-to-date
subprocess.run(['cargo', 'build', '--release'])


# %%

BENCHMARKS = [(str(path), path.name) for path in REPO_PATH.rglob('*.generated.unsat.smt2')]
BENCHMARKS.sort()

BENCHMARKS

# %%
benchmark_results = {}

for solver_cmdline in SOLVER_CMDLINES:
    benchmark_results[solver_cmdline[0]] = {}

for (benchmark_path, benchmark_name) in BENCHMARKS:
    print(f"Running script for the bench `{benchmark_name}`")
    futures = []
    for solver_cmdline in SOLVER_CMDLINES:
        solver = solver_cmdline[0]
        cmdline = list(map(lambda arg: arg if arg != '<INPUT>' else benchmark_path, solver_cmdline))
        start = time.time()
        process = Popen(cmdline, env=os.environ, stdout=PIPE, stderr=DEVNULL, text=True)
        try:
            out, _ = process.communicate(timeout=1.0)
            solved = out.strip() == 'unsat'
            if solved:
                print(f'{solver} quickly solved {benchmark_name}')
            else:
                print(f'{solver} gave up on solving {benchmark_name}')
            benchmark_results[solver][benchmark_name] = (time.time() - start) if solved else 'unsolved'
        except TimeoutExpired:
            # This problem is likely quite difficuilt
            futures.append((solver, start, process))
    
    for solver, start, process in futures:
        try:
            out, _ = process.communicate(timeout=TIME_LIMIT_SECONDS + start - time.time())
            solved = out.strip() == 'unsat'
            if solved:
                print(f'{solver} eventually solved {benchmark_name}')
            else:
                print(f'{solver} gave up on solving {benchmark_name}')
            benchmark_results[solver][benchmark_name] = (time.time() - start) if solved else 'unsolved'
        except TimeoutExpired:
            print(f"{solver} timeouted on {benchmark_name}")
            benchmark_results[solver][benchmark_name] = 'unsolved'

benchmark_results
# %%

import json
with open(REPO_PATH / 'scripts' / 'eval.json', 'w') as out:
    json.dump(benchmark_results, out, indent=2)

# %%
