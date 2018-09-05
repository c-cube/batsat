
FLAGS ?=

build: prebuild
	@cargo build --release ${FLAGS}
	@ln -sf target/release/batsat-bin

build-debug:
	@cargo build ${FLAGS}
	@ln -sf target/debug/batsat-bin

all: build test

build-ipasir:
	@cargo build --release -p batsat-ipasir

build-ocaml:
	@dune build -p batsat

test-ocaml:
	@dune runtest --force --no-buffer

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean
	@dune clean || true

test-benchs: build
	@make -C benchs

test-rust: prebuild
	@cargo test --release

test: test-rust test-benchs

prebuild:

.PHONY: prebuild check release clean

