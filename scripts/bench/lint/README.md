# The `lint` benchmark

This benchmark runs `lake exe runLinter Mathlib`.
It measures the following metrics:

- `lint//instructions`
- `lint//maxrss`
- `lint//task-clock`
- `lint//wall-clock`

It also records, for each environment linter `<name>` (from `runLinter --trace`):

- `lint/linter/<name>//heartbeats`: heartbeats summed over the linter's per-declaration tasks
- `lint/linter/<name>//task-time`: elapsed time summed over those tasks
- `lint/linter/<name>//decls`: number of declarations the linter checked

Linters run concurrently on a shared thread pool, so a linter's cost cannot be read off
wall-clock gaps in the trace; these per-task sums can.
