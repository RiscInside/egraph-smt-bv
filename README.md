# `egraph-smt-bv`

Using [egglog](https://github.com/egraphs-good/egglog) to solve SMT bitvector problems. See examples of what's currently tackleable in [solvable](./solvable/) (spoiler alert: currently not much).

Run with

```
cargo run ./solvable/add_four_two_ways.smt2 -e add_four_two_ways.out.egg -m add_four_two_ways.out.md
```

`-e add_four_two_ways.out.egg` dumps solver's execution history as runnable egglog code to `add_four_two_ways.out.egg`. You can run this code directly with `egglog` or copy it to [the browser playground](https://egraphs-good.github.io/egglog/).

`-m add_four_two_ways.out.md` dumps solver's execution history to `add_four_two_ways.out.md`.

In both cases output is updated on the go so that it's easier to see where we get stuck.
