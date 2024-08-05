SHELL=/usr/bin/env -S bash -o pipefail

TESTS := $(shell find test -name '*.lean')

.PHONY: all build test lint testdeps

all: build test

build:
	lake build

test:
	lake test -K weak.linter.setOption=true -K weak.linter.longLine=true -K weak.linter.missingEnd=true

lint: build
	env LEAN_ABORT_ON_PANIC=1 lake exe runLinter Mathlib
