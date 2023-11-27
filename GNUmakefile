TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean test/$* > test/$*.log
	@if [ -s test/$*.log ]; then \
		echo "Error: Test output is not empty"; \
		cat test/$*.log; \
		rm -f test/$*.log \
		exit 1; \
	fi
	@rm -f test/$*.log


lint: build
	env LEAN_ABORT_ON_PANIC=1 lake exe runLinter Mathlib
