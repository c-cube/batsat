
FLAGS ?=

build:
	@cargo build --release ${FLAGS}
	@ln -sf target/release/platsat-bin

build-log:
	@cd src/platsat-bin && cargo build --release ${FLAGS} --features "logging"
	@ln -sf target/release/platsat-bin

build-debug:
	@cargo build ${FLAGS}
	@ln -sf target/debug/platsat-bin

build-debug-log:
	@cd src/platsat-bin && cargo build ${FLAGS} --features "logging"
	@ln -sf target/debug/platsat-bin

dev: build test

build-ipasir:
	@cargo build --release -p platsat-ipasir

check: prebuild
	@cargo check ${FLAGS} --all --all-features

clean:
	@cargo clean

doc:
	@cargo doc

test: test-rust test-benchs test-sudoku-fast

test-benchs: build
	@make -C benchs

test-benchs-debug: build-debug
	@make -C benchs

test-rust: prebuild
	@cargo test --release --all-features

check-build-sudoku:
	@cargo check -p platsat-sudoku


SUDOKU_BENCHS_FAST= ./benchs/sudoku/sudoku.txt
SUDOKU_BENCHS_SLOW= $(SUDOKU_BENCHS_FAST) ./benchs/sudoku/top1465.txt

test-sudoku-fast: check-build-sudoku
	@./sudoku.sh $(SUDOKU_BENCHS_FAST) > .sudoku-fast.res
	@diff .sudoku-fast.res .sudoku-fast.ref # fail if not the same

test-sudoku-slow: check-build-sudoku test-sudoku-fast
	@for file in $(SUDOKU_BENCHS_SLOW) ; do ./sudoku.sh $$file > /dev/null ; done

J?=3
DATE=$(shell date +%FT%H:%M)
TEST_OPTS?= -j $(J)
TEST_TOOL=benchpress
$(TEST_TOOL)-basic: build
	@mkdir -p snapshots
	@benchpress run --prover platsat --prover minisat \
	  -c benchs/benchpress.sexp benchs/basic/ -t 10 --progress \
	  --csv snapshots/bench-basic-$(DATE)-csv $(TEST_OPTS)

$(TEST_TOOL)-sat: build
	@benchpress run -c benchs/benchpress.sexp -j 4 --timeout 10 --progress \
		benchs/ -p minisat -p platsat

.PHONY: prebuild check release clean

clippy:
	@cargo clippy --
