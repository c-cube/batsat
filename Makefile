
FLAGS ?=

build: prebuild
	@cargo build --release ${FLAGS}

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean

test-benchs: build
	./benchs/test.py

test-rust: prebuild
	@cargo test

test: test-rust test-benchs

prebuild:

.PHONY: prebuild check release clean

