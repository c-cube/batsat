
build:
	@dune build @install

check:
	@cargo check

clean:
	@dune clean
	@cargo clean

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

.PHONY: build clean prebuild
