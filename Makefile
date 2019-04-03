
FLAGS ?=

build:
	@cargo build --release ${FLAGS}
	@ln -sf target/release/batsat-bin

build-log:
	@cd src/batsat-bin && cargo build --release ${FLAGS} --features "logging"
	@ln -sf target/release/batsat-bin

build-debug:
	@cargo build ${FLAGS}
	@ln -sf target/debug/batsat-bin

build-debug-log:
	@cd src/batsat-bin && cargo build ${FLAGS} --features "logging"
	@ln -sf target/debug/batsat-bin

dev: build test

build-ipasir:
	@cargo build --release -p batsat-ipasir

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
	@cargo check -p batsat-sudoku


SUDOKU_BENCHS_FAST= ./benchs/sudoku/sudoku.txt
SUDOKU_BENCHS_SLOW= $(SUDOKU_BENCHS_FAST) ./benchs/sudoku/top1465.txt

test-sudoku-fast: check-build-sudoku
	@./sudoku.sh $(SUDOKU_BENCHS_FAST) > .sudoku-fast.res
	@diff .sudoku-fast.res .sudoku-fast.ref # fail if not the same

test-sudoku-slow: check-build-sudoku test-sudoku-fast
	@for file in $(SUDOKU_BENCHS_SLOW) ; do ./sudoku.sh $$file > /dev/null ; done

J?=3
DATE=$(shell date +%FT%H:%M)
TEST_OPTS?= -j $(J) --junit test.xml

logitest-quick:
	@mkdir -p snapshots
	@logitest run --meta=`git rev-parse HEAD` \
	  --summary snapshots/bench-$(DATE).txt \
	  --csv snapshots/bench-$(DATE).csv \
	  -c benchs/conf.toml $(TEST_OPTS)

.PHONY: prebuild check release clean

