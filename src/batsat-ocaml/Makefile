
build:
	@dune build @install

check:
	@cargo check

clean:
	@dune clean
	@cargo clean

# must create this manually, since dune won't take it as a dependency
# see https://github.com/ocaml/dune/issues/1407
cargo-config-file:
	@mkdir -p .cargo
	@cat cargo-config > .cargo/config

CAML_LIB ?= $(shell ocamlc -where)

build-rust-stubs: cargo-config-file
	@if [ "$$(uname)" = "Darwin" ]; then \
		RUSTFLAGS="-L ${CAML_LIB} -lcamlrun" cargo build --release --frozen ; \
	else \
		cargo build --release --frozen ; \
	fi

doc:
	@dune build @doc

test:
	@dune runtest --force --no-buffer

all: build test

reindent:
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make build-dev ; \
	done

.PHONY: build clean prebuild build-rust-stubs
