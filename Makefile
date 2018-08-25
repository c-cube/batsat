
FLAGS ?=

build: prebuild
	@cargo build --release ${FLAGS}
	@ln -sf target/release/ratsat-bin

all: build test

build-ipasir:
	@cargo build --release -p ratsat-ipasir

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean

test-benchs: build
	@make -C benchs

test-rust: prebuild
	@cargo test

test: test-rust test-benchs

prebuild:

.PHONY: prebuild check release clean

