# Lake `graph-extract` — handoff for future agents

This doc describes the `lake graph-extract` subcommand, what it's for, what's currently built, and what to work on next. Snapshot date: 2026-05-04. Companion docs:

- `lake_build_graph_analysis.md` — map of mathlib's build-graph dynamism (regimes 1–3); §10 enumerates every shape of dynamism the extractor must guard against.
- `lake_facets_for_extraction.md` — which Lake facets are pure (safe for cold-cache walking) vs impure (will trigger compiles). Load-bearing for extractor correctness.
- `lake_upstream_feasibility.md` — strategy for upstreaming the subcommand to leanprover/lean4.

## Purpose

The mathlib4 build is *statically reconstructible* (`lake_build_graph_analysis.md` §11.1, regime 1). `lake graph-extract` walks Lake's resolved workspace and emits structural metadata for the requested target's build closure: module list, dependency edges, package association, output paths, and per-module setup data. No compilation is triggered.

The metadata's primary consumer is **CI shard planning**: a future GHA matrix workflow uses it to partition the build closure across N runners. Each runner then invokes Lake itself (`lake cache get` + `lake build <my modules>` + `lake cache put`) — the extractor produces the *plan*, not a recipe to replace Lake's executor.

Lake itself ships a content-addressed artifact cache (`Lake.Artifact`, `Lake.CacheMap`, `lake cache get/put/add/stage`) as of v4.30. `lake build` natively consults the cache for input-hash hits and hardlinks artifacts from `cache.artifactDir` into `.lake/build` automatically. So the distributed build is shard planning + Lake's existing machinery — not a custom CAS or executor.

## Architecture

```
extract job:    lake graph-extract <target>  →  manifest + sidecars
                shard planner                →  per-runner module assignments

per-shard runner (GHA matrix worker):
  1. lake cache get [<shard's mappings>]   ← lazy fetch from Reservoir / custom service
  2. lake build <my assigned modules>       ← Lake handles hit/miss + compile
  3. lake cache put                         ← upload new artifacts

(GHA `needs:` between shard topo levels so downstream sees upstream's `cache put`.)
```

Lake's cache integration:
- `Lake.ArtifactDescr = (Hash, ext)` — `cache.artifactDir/{hash}.{ext}` (`lean4-src/src/lake/Lake/Config/Artifact.lean`).
- `Lake.CacheMap = Hash → outputs` JSONL files mapping input hashes to output artifact descriptors (`lean4-src/src/lake/Lake/Config/Cache.lean`).
- During `lake build`, Lake computes input hash, calls `(← getLakeCache).readOutputs? scope inputHash`; on hit, hardlinks artifacts into `.lake/build`; on miss, builds and calls `saveArtifact` (`lean4-src/src/lake/Lake/Build/Common.lean:459, 518`).
- `lake cache get` defaults to lazy fetch (`leanprover/lean4#12634`, 2026-03-03) — downloads mappings only; artifacts pulled during `lake build` per-module.

## Working tree layout

- `/Users/chelo/mathlib4/lean4-src/` — local checkout of `leanprover/lean4` at `v4.30.0-rc2` (matches mathlib's toolchain). All Lake-side edits live here. Branch: `graph-extract-v1`.
- `/Users/chelo/lean4/` — sibling read-only snapshot (line-number reference only). Do not edit.
- `/Users/chelo/mathlib4/` — mathlib4 working tree, branch `GraphExtract`. Holds the design docs and a thin Python harness (`scripts/lake_graph_extract.py`, `scripts/run_graph.py`).
- Prebuilt Lake binary used for testing: `/Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake`.
- Local toolchain pin: `/Users/chelo/mathlib4/lean4-src/tests/lake/lean-toolchain` → `leanprover/lean4:v4.30.0-rc2` (untracked; `lake build` from this tree must use the same toolchain Lake was compiled against).

## Current state

### Lake-side (commits on `graph-extract-v1` in `/Users/chelo/mathlib4/lean4-src`)

1. **`f703a7a0`** — extract pure argv helpers in `Build/Actions.lean`:
   - `mkLeanModuleArgs : FilePath → ModuleSetup → FilePath → ModuleArtifacts → Array String → Array String × Bool`
   - `mkCcCompileArgs : FilePath → FilePath → Array String → Array String`
   - `renderRspContents : Array String → String`
   - Existing call sites (`compileLeanModule`, `compileO`, `compileExe`) unchanged.

2. **`ac0179e3`** — `mkLinkObjArgs` in `Build/Common.lean`: `private` → `public`.

3. **`0b814ce7`** — new file `src/lake/Lake/Build/GraphExtract.lean` (~600 LoC):
   - **Schema v2** with top-level `modules : NameMap ModuleEntry` (paths interned) and per-node `import_arts : Array (ModuleName × Bool)` (references). Avoids the multi-GB blowup of an embedded-paths schema.
   - **Pure-facet walker**: uses only the `:input` facet (`computeImportArts`, `computeTransImportArtsCached`). Never calls `mod.setup.fetch` (which would compile 8326 modules on cold cache).
   - **Two-phase enumeration**: `collectClosureInputs` builds the input cache via `:input` awaits; `enumerateModuleClosure` walks it purely.
   - **Workspace placeholders**: `$WORKSPACE`, `$LAKE_HOME`, `$TOOLCHAIN`, `$TOOLCHAIN_ROOT` (most-specific-first prefix substitution).
   - **`runPreflight`**: toolchain version (advisory), per-package + per-library `precompileModules`, `extraDepTargets` allowlist (currently `[("proofwidgets", "widgetJsAll")]`).
   - **Refuses dynlibs/plugins**: `composeLeanModuleNode` errors if `setup.dynlibs` or `setup.plugins` non-empty.

4. **`64d36c68`** — CLI integration in `src/lake/Lake/CLI/Main.lean`:
   - `protected def graphExtract`, dispatch `| "graph-extract" => lake.graphExtract`.
   - Argv shape: `lake graph-extract <target> [<manifest-path> [<sidecar-dir>]]`.

5. **`49b60ec9`** — per-node sidecar emission:
   - With sidecar dir provided, write `<sidecar-dir>/<sanitized-id>.node.json` per node (full detail).
   - Main manifest emits in summary form: each node entry is `{id, kind, module, sidecar}`.
   - On Mathlib root: index 9.9 MB; sidecars 440 MB across 8313 nodes; walk in 44s (cold cache).

### Python-side (`/Users/chelo/mathlib4` branch `GraphExtract`)

- **`fc7a0b0b3a`** — `scripts/lake_graph_extract.py` slimmed 2051 → 498 LoC. Now consumes Lake's v2 manifest. Holds three regression validators (`validate-commands`, `validate-setup`, `validate-outputs`).
- **`31672675f1`** — validator fixes:
  - `validate-setup` was passing module name to `lake setup-file`; that command takes a file path. Translate via `manifest.modules[name].src`.
  - `validate-commands` regex matched `[#N]`; Lake's actual verbose-trace format is `trace: .>`. Fixed regex + filter trace lines by target source path.
  - `run_graph.py` was writing `setup.json` with `$LAKE_HOME` placeholders; `lean --setup` reads the file literally. Absolutize importArts paths before write.

These validators are kept as a regression check on continued Lake-side iteration. They are not part of the runtime distributed-build path (which uses Lake's own executor, not `run_graph.py`).

### Verified

- 175/175 nodes byte-identical between Python-extracted and Lake-extracted manifests across 4 module targets (parity check).
- Full Mathlib root walk: 8313 modules × 8313 nodes, 44s, no errors.
- `validate-commands` and `validate-setup` pass on `Mathlib.Init`.
- **Lake honours pre-populated artifacts** (Mathlib.Init test, 2026-05-04): with `.lake/build` containing upstream `.olean` + `.hash` + `.trace` sidecars, `lake build <target>` rebuilds *only* the target. This validates the per-shard runner pattern (`cache get` + `lake build`).

## What's missing / known issues

### Scope: extractor currently emits `lean_module` nodes only

- **`cc_compile`** nodes (`.c → .o`, one per module) — `mkCcCompileArgs` is exposed; walker doesn't enumerate yet.
- **`cc_link`** nodes (one per `lean_exe`) — needs `mkLinkObjArgs` (public) + `renderRspContents`. Scaffolding sketched, not wired.
- **`package_extra_dep`** nodes (proofwidgets `widgetJsAll`) — preflight allowlist names them; emission not implemented.

For the distributed-build use case these are not on the critical path: Lake's executor handles cc compile/link automatically, so the manifest doesn't need to enumerate them for the worker. They remain useful for static analysis / external tooling and for upstreaming (so `lake graph-extract` is feature-complete in the upstream PR).

### Custom-target preflight check

Iteration over `pkg.targetDecls` with field projection (`decl.kind`) on inherited-structure fields fails with "uncaught top-level build failure" on v4.30.0-rc2 — appears to be a Lean codegen quirk inside `Job.async`. Worked around by deferring the substantive custom-target check; the load-bearing checks (`precompileModules`, `extraDepTargets`, dynlibs/plugins per module) cover the dynamism mathlib uses today. Revisit on toolchain bumps.

### `mathlib_test_executable`

16k cc_compile nodes once cc_compile emission lands. Not a blocker for v1.

### Sidecar import_arts redundancy

Each sidecar embeds the full transitive `import_arts` (~1155 entries on average), which on 8313 sidecars is ~9.6M name strings — most of the 440 MB total. Possible optimization: emit only direct imports per sidecar, compute transitive closure in the consumer. Not done — current consumers expect transitive.

## Next steps

### 1. Sharding-oriented manifest output

Refactor the manifest to hold what a CI matrix planner needs and not much more:
- Module list with package association
- Direct (not transitive) import edges
- Estimated cost per module — initially source size or transitive-import count; eventually real timings fed back from previous CI runs
- Optionally a per-shard `CacheMap`-compatible mappings file so each runner can `lake cache get <mappings>` to fetch only its assigned modules

Most of this is already in the manifest; the slim-down is mechanical. The full per-node `command`/`env`/`outputs` fields can stay (harmless and useful for offline tools), but they are not load-bearing.

### 2. Static GHA matrix workflow

The actual distributed-build product. No further Lake-side work needed for the MVP:
- **`extract` job** runs `lake graph-extract` on the PR commit, computes a topo-level greedy partition across N matrix workers, emits the shard plan as a workflow artifact.
- **`build` matrix × N**: each runner does `lake cache get`, `lake build <my modules>`, `lake cache put`. Use `needs:` for ordering between topo levels.
- **CAS backend**: start with Reservoir (Lake's default service) — zero infrastructure to deploy. Move to a self-hosted endpoint only if Reservoir hosting becomes a constraint.
- **Coexistence**: mathlib's `Cache/` (Python `lake exe cache get`) stays in place for local-dev use. CI uses Lake's native cache. Migrate to native-only when `Cache/` removal lands.

### 3. cc_compile / cc_link / package_extra_dep nodes

Backlog item for upstream completeness. With Lake driving execution, these aren't on the distributed-build critical path. Implement when:
- Upstream review wants the extractor feature-complete, or
- Static-analysis consumers (offline graph tools) need them.

### 4. Custom-target preflight

When a future toolchain bump fixes the codegen issue, enable the closure-walk allowlist check (`lake_build_graph_analysis.md` §10.2): enumerate every `BuildKey` in the target's closure, verify each is on the builtin allowlist (`Lake/Build/InitFacets.lean` enumerates the universe). Anything outside means a `module_facet`/`library_facet`/custom `target` is in the closure and the walker should refuse with a §10.x reference. Lower priority than substantive checks already handle.

### 5. Upstream `lake graph-extract`

`lake_upstream_feasibility.md` covers the strategy. Lake-side commits are mergeable as-is — opt-in subcommand, no breaking API changes, only `private` → `public` promotions where helpers are reused. Upstream framing: "structural metadata for shard planning + offline graph analysis."

## Verification recipe

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

# Full Mathlib root (size + perf check)
rm -rf /tmp/sidecars-mathlib /tmp/g-mathlib.json
time /Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake graph-extract Mathlib /tmp/g-mathlib.json /tmp/sidecars-mathlib
# Expect: ~44s, ~9.9 MB index, ~440 MB sidecars
```

`LAKE_BIN` in `scripts/lake_graph_extract.py` (line 40) points at the locally-built binary. Update if the lean4-src tree moves.

## Surprising facts worth remembering

- **`mod.setup.fetch` triggers compiles** even though it nominally just composes a `ModuleSetup`. On cold cache it cascades into 8326 build jobs. The pure-facet walker (using only `:input` + path conventions) is non-negotiable for cold-cache extraction. See `lake_facets_for_extraction.md`.
- **importArts has a 1/3/4-element size lattice**: 1 (`olean` only) for non-module imports, 3 for module-style imports, 4 (adds `oleanPrivate`) for `importAll`. Walker reconstructs by branching on `(isModule, importAll)`.
- **`lake setup-file` takes a file path, not a module name.** Validators must translate via `manifest.modules[name].src`.
- **`lake build -v` trace format is `trace: .>` not `[#N]`.**
- **`lean --setup` reads setup.json literally** — `$LAKE_HOME` placeholders won't be substituted. Absolutize before write.
- **Summary-mode `graph_deps` would balloon the index back to ~290 MB** because Mathlib root has ~1155 transitive deps per module on average. Sidecars carry the full list; the index intentionally drops it.
- **Lake's cache-hit logic depends on `.hash` AND `.trace` sidecars, not just the `.olean`.** Empirically validated 2026-05-04: deleting `.olean.hash` while keeping `.olean` causes Lake to rebuild the module on the next `lake build`. Any system that materializes oleans into `.lake/build` (CAS fetcher, distributed worker, etc.) MUST also materialize the corresponding `.hash` and `.trace` sidecars. mathlib's existing `Cache/IO.lean:292–307` packs all of `{.olean, .olean.server, .olean.private, .olean.hash, .olean.server.hash, .olean.private.hash, .ilean, .ilean.hash, .ir, .ir.hash, .c, .c.hash, .trace}` for exactly this reason. Lake's native cache (`Common.lean:saveArtifact`) hardlinks all of them too.
- **Lake's native cache is brand new and stabilizing.** Schema dated 2026-03-17. ~15 PRs by tydeu (Mac Malone) since Feb 2026 covering get/put, staging, parallel transfers, hard-linking, race conditions. Re-check current behavior against these notes before relying on them for design decisions.
- **`lake cache get` defaults to lazy fetching** (`leanprover/lean4#12634`, 2026-03-03). Downloads mappings only; artifacts fetched during `lake build` per input-hash lookup. Use `--download-arts` for the old eager behavior.
