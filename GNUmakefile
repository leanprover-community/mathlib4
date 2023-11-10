TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean test/$*

lint: build
	env LEAN_ABORT_ON_PANIC=1 lake exe runMathlibLinter
