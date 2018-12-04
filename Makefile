
FLAGS ?=

build:
	@cargo build --release ${FLAGS} --no-default-features
	@ln -sf target/release/batsat-bin

build-log:
	@cargo build --release ${FLAGS} --features "logging"
	@ln -sf target/release/batsat-bin

build-debug:
	@cargo build ${FLAGS}
	@ln -sf target/debug/batsat-bin

all: build test

build-ipasir:
	@cargo build --release -p batsat-ipasir

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean

test-benchs: build
	@make -C benchs

test-benchs-debug: build-debug
	@make -C benchs

test-rust: prebuild
	@cargo test --release

test: test-rust test-benchs

.PHONY: prebuild check release clean

