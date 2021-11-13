TESTS = $(wildcard test/*.lean)
LAKE = lake
LEAN = lean

.PHONY: all build test

all: build test

build:
	$(LAKE) build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	env LEAN_PATH=build/lib $(LEAN) test/$*
