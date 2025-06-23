from pathlib import Path
import json

REPO_PATH = Path(__file__).parent.parent

with open(REPO_PATH / 'scripts' / 'eval.out.json') as eval_file:
    results = json.load(eval_file)

SURVIVOR_PLOT = REPO_PATH / 'scripts' / "survivor_plot.out.tex"

survivor_plot_file = open(SURVIVOR_PLOT, 'w')

survivor_plot_file.write('\\begin{tikzpicture}\n')
survivor_plot_file.write('\\begin{axis}[\n')
survivor_plot_file.write('    xlabel={Execution time, s},\n')
survivor_plot_file.write('    ylabel={Number of problems solved in time},\n')
survivor_plot_file.write('    width=12cm,\n')
survivor_plot_file.write('    xmin=0.025, xmax=25.6,\n')
survivor_plot_file.write('    ymin=0, ymax=35,\n')
survivor_plot_file.write(f'    xtick={{{','.join([f'{0.025 * 2**i:.1f}' for i in range(14)])}}},\n')
survivor_plot_file.write('    ytick={0,5,10,15,20,25,30,35},\n')
survivor_plot_file.write('    xmode=log,\n')
survivor_plot_file.write('    log ticks with fixed point,\n')
survivor_plot_file.write('    legend pos=north west,\n')
survivor_plot_file.write('    ymajorgrids=true,\n')
survivor_plot_file.write('    grid style=dashed,\n')
survivor_plot_file.write(']\n')

SOLVERS = [('egraph-smt-bv', 'black'), ('z3', 'red'), ('bitwuzla', 'blue'), ('cvc5', 'green')]
legend = []

for solver_path, solver_results in results.items():
    solver_name, solver_color = next(filter(lambda solver: solver[0] in solver_path, SOLVERS))
    solver_times = sorted(filter(lambda time: time != 'unsolved', solver_results.values()))
    points = [(0.0, 0)] + list(map(lambda idx_and_time: (round(idx_and_time[1] / 1000.0, 2), idx_and_time[0] + 1), enumerate(solver_times)))
    survivor_plot_file.write(f'\\addplot[color={solver_color},mark={'square' if solver_name == 'egraph-smt-bv' else 'x'}]\n')
    survivor_plot_file.write(f'coordinates{{{' '.join(map(str, points))}}};\n')
    legend.append(solver_name)

    print(solver_name, points)



survivor_plot_file.write(f'\\legend{{{', '.join(legend)}}}\n')

survivor_plot_file.write('\\end{axis}\n')
survivor_plot_file.write('\\end{tikzpicture}\n')
