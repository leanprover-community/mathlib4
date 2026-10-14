# Interpreter symbol cache experiment

This branch prepares a comparison of Lean `8001cf3a43a2de1350f6d1dcc0a51cd7e8f469ee`
with its master base, `baeedf0cbafeff325f77b76e540f09d291f6f038`.
Both compilers build Mathlib nightly-testing commit
`9151b29138f46990b9502c758ed0567ea14843e6` with the same dependency manifest.
Both builds apply `batteries-compat.patch` to the pinned Batteries dependency.
It replaces `unfold pack` with `dsimp -zeta only [pack]` in two Float proofs, so
`extract_lets` can reach the local definitions after the match reduces. The patch
changes no theorem statements. The script verifies the patched file's digest and
rejects other tracked source changes. Artifacts include the patch and its digest.
Preflight builds all of Batteries and `Mathlib.Data.String.Basic` with both compilers.
The full builds must also pass; preflight alone does not establish compatibility.

The baseline comes from Lean CI run 38580034934, Linux artifact 11902424333.
The candidate comes from the commit-specific PR release tag
`pr-release-15693-8001cf3`. The workflow verifies download digests. The script also
checks each executable's full `--githash`, the source revision, and dependency pins.
The candidate is [Lean PR #15693](https://github.com/leanprover/lean4/pull/15693).
Wait for its commit-specific Linux release before dispatching this workflow.

## Run on Mathlib CI

Publish this branch under `ci-dev/*` in `leanprover-community/mathlib4` and dispatch
`ci_dev.yml` on that branch. The `candidate_pr` input defaults to `15693`. The job uses
the Mathlib `pr` runner pool. It does not upload compiled outputs to the Mathlib cache.
It replaces the ordinary CI-dev workflow on this experiment branch only.

The default is two timing pairs on one runner, in ABBA order. A reversed dispatch
starts BAAB. Use three to five pairs to investigate a small wall-time difference;
retain every run and report the paired results and their spread. CPU savings can
be meaningful even when a small wall-time change remains within noise. Runner
sharing and thermal or load changes can still add noise; inspect the captured
runner, CPU, cgroup, affinity, and load metadata.

Every measured run starts with empty Mathlib and dependency build directories.
Dependency downloads and Lake configuration compilation occur outside the timer.
Dependency compilation and the full `lake build Mathlib` occur inside it. Lake
artifact caches are disabled. The OS page cache is not flushed; alternating order
reduces order bias. A failed build or differing module set invalidates the comparison.
These are end-to-end clean-build measurements, not elaboration-only timings.

Use `mode=profile` for a separate pair with Lean's `--profile` enabled. Its build
logs contain Lean profiler output. That mode does not calculate speedup estimates.
This is Lean's internal profiler, not an OS stack sampler or a mutex-wait profiler.
Use separate `perf` sampling on a runner that supports it if the internal profile
does not explain the CPU and system-time results.

## Local measurement

Use a new, dedicated checkout of the pinned Mathlib revision. The script deletes
that checkout's `.lake/build` and each dependency's `.lake/build` between runs.
Put matching packaged macOS toolchains in `lean-baseline` and `lean-patched` under
one directory. The exact macOS ARM64 baseline is artifact 11914309329 of the same
CI run. A candidate macOS package requires the PR's secondary-platform CI build;
the default Linux-only build cannot provide it. Alternatively, build both exact
commits locally with the same compiler and build settings. Do not compare a local
candidate with a packaged baseline and attribute the difference to this patch.
Then, from the dedicated Mathlib checkout, run:

```sh
BENCH_TOOLCHAINS=/absolute/path/to/toolchains \
BENCH_OUTPUT=/absolute/path/to/results \
BENCH_ORDER=baseline-patched BENCH_PAIRS=3 BENCH_MODE=timings \
python3 /absolute/path/to/experiment/.github/benchmarks/interp-symbol-cache.py
```

Run on AC power, keep other builds idle, and use the same thread settings for both
variants. Start with the default settings, then repeat with `LEAN_NUM_THREADS=1`
to look for a serial regression. Do not reuse the current v4.35.0-rc3 Mathlib
outputs for the rebased compiler. For cheaper per-file measurements, first build
compatible dependencies, save a randomly selected module list, warm both variants,
and alternate their order with the profiler disabled.

## Shard count

Keep 64 as an internal compile-time constant until measurements justify a change.
Compare the original master implementation with experimental builds using 1, 16,
64, and 256 shards. One shard isolates the benefit of shorter lock scope and a
plain mutex from the benefit of sharding; it is not the original baseline.
Keep any compile-time override on the experiment branch. A user-facing Lean option
would be misleading because this cache is process-global, while Lean options can
vary by interpreter. A runtime selector also adds work to the lookup path.
