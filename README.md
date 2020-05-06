# BatSat [![build status]](https://travis-ci.org/c-cube/batsat) [![Latest Version]](https://crates.io/crates/batsat)

[build status]: https://api.travis-ci.org/c-cube/batsat.svg?branch=master
[Latest Version]: https://img.shields.io/crates/v/batsat.svg

This is a Rust SAT solver forked from [ratsat](https://github.com/qnighy/ratsat), a reimplementation of MiniSat.

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
