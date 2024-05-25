#!/bin/sh

cargo build --release -p platsat-sudoku || exit 1

export RUST_LOG=info
#export RUST_LOG=debug

export PROPAGATE=1
#export PROPAGATE=0

exec ./target/release/platsat-sudoku $@
