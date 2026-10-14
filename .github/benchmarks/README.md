# Imported unfolding benchmark

This experiment compares Lean PR 15670 with its exact parent commit. It uses the
published Linux PR release and the Linux release artifact from the parent's CI run.
The script verifies both Lean commit hashes before it builds Mathlib.

The CI-dev workflow measures two clean `lake build Mathlib` runs on the same Mathlib
`pr` runner with Lean's default CPU parallelism. The dispatch input selects the run
order. A second pair is optional if the first result needs confirmation. Dependency downloads
and configuration compilation occur before each timer starts. Dependency builds,
Mathlib elaboration, and the default library build outputs remain inside the timer.
Both runs use the same manifest pins. The script deletes every package's build
directory before each measurement and disables Lake artifact caches.

The script applies `batteries-compat.patch` to both versions. The Float proofs use
`dsimp -zeta only [pack]` to reduce the match and preserve the let bindings. The
String proofs use the public order lemmas for Lean's current comparison function.
These adaptations fix failures in the pinned dependency with the newer toolchains.
The Mathlib String order proofs also use the current core lemmas and the standard
`LinearOrder.ofStd` factory. Both toolchains build this same adapted source.

The script checks all dependency libraries and all Mathlib String modules with
both toolchains before either full build. It then deletes their build outputs
before each timed run. Lake uses `--fail-fast` so a failed target stops new build jobs. The script verifies that
the source remains unchanged between measurements. A failed build does not produce
a speedup estimate.

The job uploads logs, CPU and memory details, module lists, wall times, user CPU
times, and system CPU times. Reverse the order in a second dispatch to check run-order effects.
These are full build measurements, separate from the Batteries linter measurements.

This branch replaces `ci_dev.yml` for this experiment only. It accepts manual
dispatches on `ci-dev/*` branches of `leanprover-community/mathlib4`. It does not
upload compiled artifacts to the Mathlib cache. Lake and Lean run inside landrun;
only the dependency download has network access. They have no credentials and can
write only job-local outputs and `.lake`.

The earlier four-thread experiment in the fork was cancelled before a complete
comparison. Its nightly-testing PR is closed. This experiment does not run CI in
the nightly-testing repository.
