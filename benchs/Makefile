
TEST_TOOL=./test_tool.exe
TIMEOUT ?= 10
J ?= 3
#CHECKER ?= 
CHECKER ?= CHECKER=./drat-trim

all: run_tests

run_tests: build drat-trim
	TIMEOUT=$(TIMEOUT) JOBS=$(J) $(CHECKER) $(TEST_TOOL)

build:
	@cd test_tool && cargo build --release
	@ln -sf test_tool/target/release/test_tool $(TEST_TOOL)

drat-trim: drat/drat-trim.c
	gcc -O2 $< -o $@

clean:
	@cargo clean
