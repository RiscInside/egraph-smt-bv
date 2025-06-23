from pathlib import Path
import json

REPO_PATH = Path(__file__).parent.parent

with open(REPO_PATH / 'scripts' / 'width.out.json') as eval_file:
    results = json.load(eval_file)

SOLVERS = [('egraph-smt-bv', 'black'), ('z3', 'red'), ('bitwuzla', 'blue'), ('cvc5', 'green')]

for (benchmark_name, per_solver_results) in results.items():
    benchmark_tex = REPO_PATH / 'scripts' / benchmark_name.replace('.tmp.smt2', '.width.out.tex')
    with open(benchmark_tex, 'w') as benchmark_file:
        benchmark_file.write('\\begin{tikzpicture}\n')
        benchmark_file.write('\\begin{axis}[\n')
        benchmark_file.write('    xlabel={Width of the datapath, bits},\n')
        benchmark_file.write('    ylabel={Execution time, s},\n')
        benchmark_file.write('    width=6cm,\n')
        benchmark_file.write(f'    xmin=0, xmax={32 if 'squared_difference' in benchmark_name else 256},\n')
        benchmark_file.write('    ymin=0, ymax=300,\n')
        benchmark_file.write(f'    xtick={{{','.join(map(str, range(32, 256 + 32, 32)))}}},\n')
        benchmark_file.write(f'    ytick={{{','.join(map(str, range(30, 300 + 30, 30)))}}},\n')
        benchmark_file.write('    legend pos=north west,\n')
        benchmark_file.write('    ymajorgrids=true,\n')
        benchmark_file.write('    grid style=dashed,\n')
        benchmark_file.write(']\n')

        legend = []
        for (solver_path, results) in per_solver_results.items():
            solver_name, solver_color = next(filter(lambda solver: solver[0] in solver_path, SOLVERS))

            benchmark_file.write(f'\\addplot[color={solver_color},mark={'square' if solver_name == 'egraph-smt-bv' else 'x'}]\n')
            benchmark_file.write(f'coordinates{{{' '.join(map((lambda coords: str((coords[0], round(coords[1] / 1000, 2)))), filter(lambda time: time[1] != 'unsolved', results)))}}};\n')
            legend.append(solver_name)
            

        benchmark_file.write('\\end{axis}\n')
        benchmark_file.write('\\end{tikzpicture}\n')
