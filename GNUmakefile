TESTS = $(wildcard test/*.lean)

.PHONY: all build test lint

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	lake env lean test/$*

lint: build
	./build/bin/runLinter
