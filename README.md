# PlatSat
This is a Rust SAT solver forked from [batsat](https://github.com/c-cube/batsat) forked from [ratsat](https://github.com/qnighy/ratsat), a reimplementation of MiniSat.

For reference, a [simple benchmark](https://benchpress.cedeela.fr/show/res-20220112T143715-921dc3ad-f9fa-493d-8a08-540eecad9827.sqlite/) comparing it to minisat on a set of (easy) problems.

## License

MIT licensed.

## Features and Goals

Batsat is originally based on ratsat, a clone of minisat. However we want
to extend batsat further and to provide the following features:

- [x] proof production (in [DRAT](https://baldur.iti.kit.edu/sat-competition-2017/index.php?cat=certificates))
- [x] easy access to unsat-cores (as subset of assumptions)
- [x] ipasir interface for incremental solving
  * [ ] testing this interface
- [x] debug framework using `log` (optional)
- [x] OCaml bindings
- [x] templated API to write SMT solvers
- [ ] simplification techniques from Minisat+ (as an optional internal structure)

Platsat extends batsat by making it safe (`#![forbid(unsafe_code)]`) and `no_std`, as well as improving the SMT solver API
