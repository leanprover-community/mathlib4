# Mathlib4 benchmark suite

This directory contains the mathlib4 benchmark suite.
It is built around [radar](github.com/leanprover/radar)
and benchmark results can be viewed
on the [Lean FRO radar instance](https://radar.lean-lang.org/repos/mathlib4).

To execute the entire suite, run `scripts/bench/run` in the repo root.
To execute an individual benchmark, run `scripts/bench/<benchmark>/run` in the repo root.
All scripts output their measurements into the file `measurements.jsonl`.

Radar sums any duplicated measurements with matching metrics.
To post-process the `measurements.jsonl` file this way in-place,
run `scripts/bench/combine.py` in the repo root after executing the benchmark suite.

The `*.py` symlinks exist only so the python files are a bit nicer to edit
in text editors that rely on the file ending.
