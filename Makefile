
FLAGS ?= 

build: prebuild
	@cargo build --release ${FLAGS}

check: prebuild
	@cargo check ${FLAGS}

clean:
	@cargo clean

prebuild:

.PHONY: prebuild check release clean

