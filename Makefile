
FLAGS ?= 

build: prebuild
	@cargo build --release ${FLAGS}

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean

test: build
	./benchs/test.py

prebuild:

.PHONY: prebuild check release clean

