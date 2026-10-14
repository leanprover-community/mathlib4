# Imported unfolding benchmark

This experiment compares Lean PR 15670 with its exact parent commit. It uses the
published Linux PR release and the Linux release artifact from the parent's CI run.
The script verifies both Lean commit hashes before it builds Mathlib.

Two jobs use opposite run orders. Each job measures two clean `lake build Mathlib`
runs on the same GitHub-hosted runner with `LEAN_NUM_THREADS=4`. Dependency downloads
and configuration compilation occur before each timer starts. Dependency builds,
Mathlib elaboration, and the default library build outputs remain inside the timer.
Both runs use the same manifest pins. The script deletes every package's build
directory before each measurement and disables Lake artifact caches.

The script first checks `Batteries.Data.Float.Lemmas` with both toolchains. This
module currently fails in nightly CI. A failed check stops the experiment before
the full builds. A failed full build does not produce a speedup estimate.

Each job uploads logs, CPU and memory details, module lists, wall times, user CPU
times, and system CPU times. Compare the two job summaries to check run-order effects.
These are full build measurements, separate from the Batteries linter measurements.

The workflow runs only on the experiment branch in `marcelolynch/mathlib4`.
The standard Mathlib CI workflows and their toolchain restrictions stay unchanged.
