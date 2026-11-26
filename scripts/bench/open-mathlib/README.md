# The `open-mathlib` benchmark

This benchmark approximates `import Mathlib` in the editor by running `lake lean Mathlib.lean`.
It measures the following metrics:

- `open-mathlib//instructions`
- `open-mathlib//maxrss`
- `open-mathlib//task-clock`
- `open-mathlib//wall-clock`
