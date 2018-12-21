
FLAGS ?=

build:
	@cargo build --release ${FLAGS}
	@ln -sf target/release/batsat-bin

# NOTE: doesn't work yet, see https://github.com/rust-lang/cargo/issues/5015
build-log:
	@cargo build --release ${FLAGS} --features "batsat/logging batsat-bin/logging"
	@ln -sf target/release/batsat-bin

build-debug:
	@cargo build ${FLAGS}
	@ln -sf target/debug/batsat-bin

all: build test

build-ipasir:
	@cargo build --release -p batsat-ipasir

check: prebuild
	@cargo check ${FLAGS} --all-features

clean:
	@cargo clean

doc:
	@cargo doc

test-benchs: build
	@make -C benchs

test-benchs-debug: build-debug
	@make -C benchs

test-rust: prebuild
	@cargo test --release --all-features

test: test-rust test-benchs

.PHONY: prebuild check release clean

