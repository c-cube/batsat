#!/bin/sh

cargo build -p platsat-sudoku || exit 1

#export RUST_LOG=info
export RUST_LOG=trace
export RUST_BACKTRACE=1

export PROPAGATE=1
#export PROPAGATE=0

exec ./target/debug/platsat-sudoku $@
