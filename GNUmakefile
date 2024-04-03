SHELL=/usr/bin/env -S bash -o pipefail

TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint

all: build test

build:
	lake build

testdeps:
	# add any extra targets that tests depend on here
	lake build ProofWidgets

test: $(addsuffix .run, $(TESTS))

test/%.run: build testdeps
	lake env lean test/$* | scripts/check_silent.sh test/$*.log

lint: build
	env LEAN_ABORT_ON_PANIC=1 lake exe runLinter Mathlib
