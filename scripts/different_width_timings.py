# %%
import subprocess

import json
import time
import os
import shutil
from pathlib import Path
from subprocess import Popen, DEVNULL, PIPE, TimeoutExpired

# %%

TIME_LIMIT_SECONDS = 600
# 4gb in kb
MEMORY_LIMIT = 4194304
REPO_PATH = Path(__file__).parent.parent
assert not (REPO_PATH / 'scripts' / 'width.out.json').exists(), "Move old width.out.json file to avoid overwrite"

SOLVER_PATH = REPO_PATH / 'target' / 'release' / 'egraph-smt-bv'
# Must be in path
SOLVER_CMDLINES = [[str(SOLVER_PATH), '<INPUT>', '-t', str(TIME_LIMIT_SECONDS * 1000)], ['z3', f'-T:{TIME_LIMIT_SECONDS}', '<INPUT>']]

if 'BITWUZLA_PATH' in os.environ:
    BITWZULA_PATH = os.environ['BITWZULA_PATH']
else:
    BITWZULA_PATH = shutil.which('bitwuzla')

if 'CVC5_PATH' in os.environ:
    CVC5_PATH = os.environ['CVC5_PATH']
else:
    CVC5_PATH = shutil.which('cvc5')

if BITWZULA_PATH:
    SOLVER_CMDLINES.append([BITWZULA_PATH, '-t', str(TIME_LIMIT_SECONDS), '<INPUT>'])

if CVC5_PATH:
    SOLVER_CMDLINES.append([CVC5_PATH, f'--tlimit={TIME_LIMIT_SECONDS * 1000}', '<INPUT>'])

print(SOLVER_CMDLINES)

REPO_PATH, SOLVER_CMDLINES

# %%

# Making sure that solver's binary is up-to-date
subprocess.run(['cargo', 'build', '--release'])


# %%

TEMPLATES = [
    [REPO_PATH / 'scripts' / 'add_or_and.tmp.smt2', list(range(32, 256 + 32, 32))],
    [REPO_PATH / 'scripts' / 'fast_absolute_value.tmp.smt2', list(range(32, 256 + 32, 32))],
    [REPO_PATH / 'scripts' / 'squared_difference.tmp.smt2', list(range(6, 14)) + list(range(14, 32, 5))]]

BENCHMARKS = []
for template_path, template_widths in TEMPLATES:
    with open(template_path) as template_file:
        template_source = template_file.read()
    
    for width in template_widths:
        bench_source = template_source.replace('<WIDTH>', str(width))
        bench_path = str(template_path).replace('.tmp.smt2', f'.{width}.out.smt2')
        with open(bench_path, 'w') as bench_file:
            bench_file.write(bench_source)
        BENCHMARKS.append((bench_path, str(template_path).split('/')[-1], width))

# %%
benchmark_results = {}

for benchmark_path, benchmark_name, benchmark_width in BENCHMARKS:
    if benchmark_name not in benchmark_results:
        benchmark_results[benchmark_name] = {}

    print(f"Running script for the bench {benchmark_name} and width {benchmark_width} (`{benchmark_path}`)")
    futures = []
    for solver_cmdline in SOLVER_CMDLINES:
        solver = solver_cmdline[0]

        if solver not in benchmark_results[benchmark_name]:
            benchmark_results[benchmark_name][solver] = []

        cmdline = f'ulimit -Sv {MEMORY_LIMIT} && ulimit -Hv {MEMORY_LIMIT} && ' + ' '.join(list(map(lambda arg: arg if arg != '<INPUT>' else benchmark_path, solver_cmdline)))
        print(cmdline)

        if len(benchmark_results[benchmark_name][solver]) > 0 and benchmark_results[benchmark_name][solver][-1][1] == 'unsolved':
            continue

        start = time.time()
        process = Popen(cmdline, env=os.environ, stdout=PIPE, stderr=DEVNULL, text=True, shell=True)
        try:
            out, err = process.communicate(timeout=1.0)
            assert out.strip() != 'sat'

            solved = out.strip() == 'unsat'
            if solved:
                print(f'{solver} quickly solved {benchmark_path}')
            else:
                print(f'{solver} gave up on solving {benchmark_path}')
            benchmark_results[benchmark_name][solver].append((benchmark_width, round(1000 * (time.time() - start), 2) if solved else 'unsolved'))
        except TimeoutExpired:
            # This problem is likely quite difficuilt
            futures.append((solver, start, process))
    
    for solver, start, process in futures:
        try:
            out, _ = process.communicate(timeout=TIME_LIMIT_SECONDS + start - time.time())
            assert out.strip() != 'sat'

            solved = out.strip() == 'unsat'
            if solved:
                print(f'{solver} eventually solved {benchmark_path}')
            else:
                print(f'{solver} gave up on solving {benchmark_path}')
            benchmark_results[benchmark_name][solver].append((benchmark_width, round(1000 * (time.time() - start), 2) if solved else 'unsolved'))
        except TimeoutExpired:
            print(f"{solver} timeouted on {benchmark_path}")
            benchmark_results[benchmark_name][solver].append((benchmark_width, 'unsolved'))
    
    with open(REPO_PATH / 'scripts' / 'width.out.json', 'w') as out:
        json.dump(benchmark_results, out, indent=2)

# %%
