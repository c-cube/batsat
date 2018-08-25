
TEST_TOOL=./test_tool.exe
TIMEOUT ?= 10
J ?= 3

all: run_tests

run_tests: build
	TIMEOUT=$(TIMEOUT) JOBS=$(J) $(TEST_TOOL)

build:
	@cd test_tool && cargo build
	@ln -sf test_tool/target/debug/test_tool $(TEST_TOOL)

clean:
	@cargo clean
