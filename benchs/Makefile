
TEST_TOOL=./test_tool.exe
TIMEOUT ?= 10

all: build
	TIMEOUT=$(TIMEOUT) $(TEST_TOOL)

build:
	@cd test_tool && cargo build
	@ln -sf test_tool/target/debug/test_tool $(TEST_TOOL)

clean:
	@cargo clean
