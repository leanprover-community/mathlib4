# Prompt for the next agent

You are picking up work on a distributed-build pipeline for mathlib4, built around a new `lake graph-extract` subcommand. Read this whole document before doing anything.

## Context in one paragraph

mathlib4's CI build is slow because every PR rebuilds modules that the toolchain hasn't changed. The plan is a distributed CI built on GHA matrix workers + Lake's native artifact cache (`Lake.Artifact`, `lake cache get/put`, landed in v4.30). A new `lake graph-extract` subcommand emits structural metadata for the build closure of any target; a downstream shard planner partitions the closure across N runners; each runner does `lake cache get` + `lake build <my modules>` + `lake cache put`. Lake itself executes; the extractor only plans.

## Read these first, in order

1. **`lake_graph_extract_handoff.md`** — this is the operational ground truth. Working-tree layout, what's committed, what's missing, verification recipe, surprising facts. **Read all of it.** Do not skip the "Surprising facts" section — it has empirical findings (notably about cache-hit sidecars and impure facets) that have already cost us cycles.
2. **`lake_graph_extract.md`** — design reference for the subcommand. Schema, architecture, validation harness.
3. **`lake_facets_for_extraction.md`** — the pure/impure facet boundary. The walker's correctness depends on this. Skim §1–§3.
4. **`lake_build_graph_analysis.md`** — long. The load-bearing parts are §10 (dynamism guards) and §11 (regime classification). The rest is reference material; consult as needed.
5. **`lake_upstream_feasibility.md`** — only when you're ready to think about the upstream PR.

## Working tree

- **`/Users/chelo/mathlib4/lean4-src/`** — local checkout of `leanprover/lean4` at `v4.30.0-rc2` (matches mathlib's toolchain). All Lake-side edits go here. Branch: `graph-extract-v1`. Five commits ahead of `master`.
- **`/Users/chelo/mathlib4/`** — mathlib4, branch `GraphExtract`. Holds the docs and a thin Python regression harness (`scripts/lake_graph_extract.py`, `scripts/run_graph.py`).
- **Prebuilt Lake binary** for testing: `/Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake`.
- **Local toolchain pin** (untracked, must exist): `/Users/chelo/mathlib4/lean4-src/tests/lake/lean-toolchain` → `leanprover/lean4:v4.30.0-rc2`.
- **`/Users/chelo/lean4/`** — read-only sibling snapshot. Do not edit.

## What's currently working

- `lake graph-extract <target> [<manifest> [<sidecar-dir>]]` walks the workspace using only pure facets, emits a v2 manifest (interned modules + per-node import_arts references) and optional per-node sidecars.
- Full Mathlib root walk: 8313 modules, 44s, 9.9 MB index manifest + 440 MB sidecars.
- Three regression validators (`validate-commands`, `validate-setup`, `validate-outputs` in `scripts/lake_graph_extract.py`) confirm byte-identical agreement with `lake build` on the modules tested.
- Empirically validated: with upstream `.olean` + `.hash` + `.trace` sidecars present in `.lake/build`, `lake build <target>` rebuilds *only* the target. This is the load-bearing property for the per-shard runner pattern.

## What you should do — pick one of these

### Path A: Sharding-oriented manifest output (highest user value)

Slim the manifest down to what a CI matrix planner needs:
- Module list with package association
- Direct (not transitive) import edges
- Estimated cost per module — start with source size or transitive-import count
- Optionally: per-shard `CacheMap`-compatible mappings file so each runner can `lake cache get <mappings>` to fetch only its assigned modules

Most of this data is already in the manifest; the work is mechanical refactoring + adding a cost estimate. After this lands, work moves to the GHA workflow itself, which is mathlib-side and outside Lake's scope.

### Path B: Custom-target preflight check

Currently deferred due to a v4.30.0-rc2 codegen issue: iteration over `pkg.targetDecls` with field projection on inherited-structure fields fails inside `Job.async`. If you hit this, it's not your code — it's a Lean codegen quirk. Workaround: write the check without the `Job.async` wrapper if possible, or wait for a toolchain bump. This is lower priority than Path A.

### Path C: Upstreaming the subcommand

Read `lake_upstream_feasibility.md`. The five commits on `graph-extract-v1` are designed to be mergeable as-is. The two open items before opening the PR (custom-target preflight and cc_compile/cc_link nodes) can be left as follow-ups; "land minimal first" is the recommended path.

## Things to NOT do

- **Do not implement custom SHA256 / cache_key.** Lake's `Hash` infrastructure is the canonical input hash. Reimplementing is wasted work.
- **Do not extend `run_graph.py` as a runtime executor.** Lake is the executor. `run_graph.py` exists only to validate the extractor end-to-end.
- **Do not build a custom CAS or P2P artifact protocol.** Lake's `cache.artifactDir` + `lake cache get/put` already handles content-addressed remote caching. Reservoir is the default service; custom HTTP endpoints are configurable.
- **Do not call `mod.setup.fetch`, `mod.exportInfo.fetch`, or any artifact-bearing facet from the walker.** They trigger compiles even though some have `buildable := false`. See `lake_facets_for_extraction.md` §3.
- **Do not write `.olean` files into `.lake/build` without their `.hash` and `.trace` sidecars.** Lake's cache-hit logic depends on the sidecars; missing sidecars cause spurious rebuilds.
- **Do not hand-mirror Lake source if a public helper exists.** `mkLeanModuleArgs`, `mkCcCompileArgs`, `mkLinkObjArgs`, `renderRspContents` are all public now (commits `f703a7a0` and `ac0179e3`); call them.

## Verification recipe (run after every Lake-side change)

```bash
# Rebuild Lake from the local lean4-src tree
cd /Users/chelo/mathlib4/lean4-src/tests/lake && lake build

# Smoke test: Mathlib.Init with sidecars
cd /Users/chelo/mathlib4
rm -rf /tmp/sidecars-init /tmp/g-init.json
/Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake graph-extract Mathlib.Init /tmp/g-init.json /tmp/sidecars-init

# Regression validators
python3 scripts/lake_graph_extract.py validate-commands Mathlib.Init
python3 scripts/lake_graph_extract.py validate-setup    Mathlib.Init
python3 scripts/lake_graph_extract.py validate-outputs  Mathlib.Init

# Full Mathlib root (size + perf check). Expect ~44s, ~9.9 MB index, ~440 MB sidecars.
rm -rf /tmp/sidecars-mathlib /tmp/g-mathlib.json
time /Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake graph-extract Mathlib /tmp/g-mathlib.json /tmp/sidecars-mathlib
```

If the validators fail or the walk takes more than ~60s, something is wrong. The most likely culprit is accidentally calling an impure facet. Bisect by reading the verbose Lake output (`lake build -v` is verbose; the walker also has `LAKE_DEBUG`-style flags you can grep for).

## Communication protocol

The user has a strong preference for staged work — propose a plan, get agreement, implement, verify, commit. Don't bundle multiple unrelated changes into one commit. The five commits on `graph-extract-v1` are good models: each is independently revertable.

If the user expresses frustration or pushes back, **stop and ask** rather than retrying. The pushback usually contains information — they've often found something you missed.

When you finish a chunk of work, update `lake_graph_extract_handoff.md` so the *next* agent doesn't have to re-derive what you learned.
