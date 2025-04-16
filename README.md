# `egraph-smt-bv`

Using [egglog](https://github.com/egraphs-good/egglog) to solve (UNSAT) SMT problems in theory of FixedSizeBitVectors.

See SMT2LIB examples of some tacklable problems in [tests/unsat](./tests/unsat).

With the help of [yosys](https://github.com/YosysHQ/yosys), `egraph-smt-bv` can be used to verify equivalence of two designs. See examples of verilog designs from [RTLRewriter-Bench](https://github.com/yaoxufeng/RTLRewriter-Bench) that we can prove equivalence of in [tests/verilog](./tests/verilog).

## Usage

`egraph-smt-bv` tries to behave like a spec-compliant SMT2LIB solver, though in practice support for various commands/options is lacking. You can run an SMT2LIB file with:

```
cargo run <path.smt2>
```

The only command currently producing output is `(check-sat)`, which will either return `unsat` or `unknown`.

Only core and bitvector theories are supported.
