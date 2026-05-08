# `lake graph-extract` — design reference

Companion to [`lake_build_graph_analysis.md`](./lake_build_graph_analysis.md). The analysis doc establishes that mathlib4's Lake build is *statically reconstructible* (regime 1, §11). This doc covers the schema, architecture, and validation harness for the `lake graph-extract` subcommand that emits the static graph.

For the current implementation status, the working-tree layout, and the commit-by-commit history of what was built, see [`lake_graph_extract_handoff.md`](./lake_graph_extract_handoff.md). For the wider distributed-build context (Lake's native cache, GHA matrix sharding), also see the handoff doc.

---

## 1. What it produces

`lake graph-extract <target> [<manifest-path> [<sidecar-dir>]]` walks the resolved workspace and emits structural metadata for the requested target's build closure. The output is split between an aggregated manifest and (optionally) per-node sidecar files.

The manifest's primary consumer is **CI shard planning**: a downstream tool partitions the closure across N matrix runners. The execution itself is delegated to Lake — runners call `lake build`, which honours Lake's native artifact cache automatically. The manifest is structural data, not a recipe to replace Lake's executor.

---

## 2. Workspace assumptions (preflight)

The walker refuses to operate unless the workspace is in regime 1 (analysis doc §11.1). The internal `runPreflight` step encodes:

- Toolchain version (`lake --version` ↔ `lean-toolchain`) — currently advisory.
- No `precompileModules := true` on any active package or library (§10.1).
- All `extraDepTargets` are on a small allowlist; mathlib's only entry today is `("proofwidgets", "widgetJsAll")` (§10.4).
- Per-module `setup.dynlibs` and `setup.plugins` empty for every walked module (§10.5).

Custom-target / custom-facet detection (`module_facet`/`library_facet`/non-builtin `target` declarations) is currently deferred — see the handoff doc's "What's missing" section for the codegen issue blocking that check on v4.30.0-rc2. The substantive checks above cover the dynamism mathlib uses today.

Active packages and libs are read from the elaborated `Workspace`, not from `.lake/packages/` or `lake-manifest.json`. This filters out stale resolution residue (e.g. `lean4-cli` shadowed by `Cli`) by construction.

---

## 3. Schema

The manifest uses a v2 layout: top-level `modules` index (paths interned, one entry per module) plus per-node `import_arts` references.

```json
{
  "version": "v2",
  "target": "Mathlib.Init",
  "deps_mode": "transitive" | "immediate",
  "form": "summary" | "full",
  "workspace": {
    "WORKSPACE": "/abs/path/to/repo",
    "LAKE_HOME": "/abs/path/to/repo/.lake",
    "TOOLCHAIN": "/abs/path/to/toolchain/bin",
    "TOOLCHAIN_ROOT": "/abs/path/to/toolchain"
  },
  "module_count": 8313,
  "modules": {
    "Mathlib.Init": {
      "src": "$WORKSPACE/Mathlib/Init.lean",
      "package": "mathlib",
      "isModule": true,
      "olean": "$LAKE_HOME/build/lib/lean/Mathlib/Init.olean",
      "oleanServer": "$LAKE_HOME/build/lib/lean/Mathlib/Init.olean.server",
      "oleanPrivate": "$LAKE_HOME/build/lib/lean/Mathlib/Init.olean.private",
      "ir": "$LAKE_HOME/build/lib/lean/Mathlib/Init.ir",
      "setupJsonPath": "$LAKE_HOME/build/ir/Mathlib/Init.setup.json",
      "leanOptions": { ... }
    },
    ...
  },
  "node_count": 8313,
  "nodes": [
    // summary form (when sidecars are emitted):
    { "id": "mathlib:Mathlib.Init", "kind": "lean_module", "module": "Mathlib.Init", "sidecar": "mathlib_Mathlib.Init.node.json" }

    // full form (no sidecars):
    // { "id": "...", "kind": "lean_module", "module": "...", "command": [...], "env": {...},
    //   "outputs": [...], "import_arts": [["Mathlib.Tactic.Lemma", false], ...] }
  ]
}
```

### Sidecar files

When invoked with a third positional argument, `graph-extract` writes `<sidecar-dir>/<sanitized-id>.node.json` per node. Each sidecar holds the full per-node record (`command`, `env`, `outputs`, `import_arts`). The main manifest then carries only the slim summary entries above.

Sanitization: `:`, `/`, `@`, `+` → `_`. Stable: same id always sanitizes the same way.

### Path placeholders

The graph uses POSIX-style placeholders for portability:

| Placeholder | Substitutes |
|---|---|
| `$WORKSPACE` | repo root |
| `$LAKE_HOME` | `$WORKSPACE/.lake` |
| `$TOOLCHAIN` | toolchain `bin/` directory |
| `$TOOLCHAIN_ROOT` | toolchain root |

Resolution is most-specific first (`LAKE_HOME` matches before `WORKSPACE`; `TOOLCHAIN` before `TOOLCHAIN_ROOT`). The `@<path>` rsp-arg form is handled specially: the `@` prefix is preserved, the path part is relativized.

The `workspace` field records the absolute paths the placeholders should resolve to on the emitter's machine; a worker on a different machine overrides these and re-absolutizes.

---

## 4. Architecture

### 4.1 Pure-facet walker

The extractor must operate on a cold `.lake/build` without triggering compiles. This rules out `:setup`, `:importArts`, `:exportInfo`, and any other artifact-bearing facet. Only the `:input` facet (and its derivatives `:imports`, `:transImports`) is pure (see `lake_facets_for_extraction.md`).

The walker is therefore two-phase:
1. **`collectClosureInputs`** — fetches `:input` for every module reachable from the target. Each fetch reads source headers only (`IO.FS.readFile` + `Lean.parseImports'`); no compile is triggered.
2. **`enumerateModuleClosure`** — walks the populated input cache purely. Reconstructs `ImportArtifacts` from path conventions (the 1/3/4-element size lattice based on `(isModule, importAll)`); reconstructs `setup.json` content directly.

### 4.2 Reconstructed setup.json

`setup.json` content is composed at extraction time from:
- The module's name + package + `isModule` flag (from `:input` headers).
- Per-library `leanOptions` (from `LeanLibConfig` — direct workspace access, not a facet).
- A flag-filtered transitive walk over imports (mirrors Lake's `fetchTransImportArts`: filter on `isExported || importAll`; track strongest `importAll` per module; collapse non-module-style importers via the `nonModule` flag).
- Empty `dynlibs` and `plugins` (forced by the preflight invariant).

The on-disk file is *not* written by the extractor. Its path is recorded as both an `output` (it must be written by the executor before invoking `lean --setup`) and embedded in `node.setup_json` so a downstream tool can materialize it.

### 4.3 Argv composition

For `lean_module` nodes, the argv is built by `mkLeanModuleArgs` (a pure helper exposed from `Lake/Build/Actions.lean`). Same shape as `compileLeanModule` minus I/O side effects:

```
$TOOLCHAIN/lean <src.lean> -o <olean> -i <ilean> -c <c-out> [-b <bc-out>] --setup <setup.json> --json
```

For cc nodes (not yet emitted), `mkCcCompileArgs` and `mkLinkObjArgs` (also exposed) compose the cc compile / cc link argv from Lake's own internals.

### 4.4 LEAN_PATH

Read directly from the elaborated `Workspace` (`ws.augmentedLeanPath`). No hand-curated package-order table.

### 4.5 Toolchain paths and cc flags

Read from `ws.lakeEnv.lean.{binDir, sysroot, includeDir, leanLibDir, ccFlags, ccLinkFlags}`. No empirical capture of cc flag lists.

---

## 5. Validation harness

`scripts/lake_graph_extract.py` is a thin Python script (~500 LoC) that consumes the v2 manifest and exercises three regression validators. It is not a runtime tool for the distributed build (Lake itself is the executor); it's a regression check on the extractor's correctness during continued Lake-side iteration.

### 5.1 `validate-commands <module>`

Byte-exact diff between the extractor's argv (after placeholder substitution) and `lake build -v`'s actual `lean` invocation for the same module. Catches drift in:
- LEAN_PATH order or contents
- Output path conventions (e.g. Lake adding `.bc` for the LLVM backend)
- Per-lib `leanArgs` / `weakLeanArgs` going non-static

Destructive: deletes the module's outputs first so Lake actually runs `lean` (not `Replayed`). Lake regenerates them.

### 5.2 `validate-setup <module>`

Semantic JSON diff between the extractor's reconstructed `setup.json` and `lake setup-file <src.lean>`'s output. Catches drift in:
- Transitive-import filter rules (`fetchTransImportArts` mirroring)
- Per-lib options propagation
- `isModule` / `plugins` / `dynlibs` flags
- The 1/3/4-element importArts size lattice

Byte equivalence is not required (Lake's `Lean.Json` emission order is implementation-defined); semantic equivalence is the correctness criterion.

### 5.3 `validate-outputs <target> [--full]`

End-to-end byte equivalence of build outputs: extract → delete the target's outputs → run `run_graph.py` (a sequential reference executor that consumes the manifest) → hash rebuilt outputs → diff against pre-existing golden hashes.

Excluded from the diff: `*.hash`, `*.trace`, `*.rsp`, `*.setup.json` (Lake writes hash/trace sidecars with its own scheme that the reference executor doesn't replicate; rsp byte form is verified separately for the same arg list; setup.json byte-form depends on emission order — semantic equivalence is enforced by `validate-setup`, and downstream artifacts reproduce byte-exactly because `lean --setup` parses semantically).

The reference executor `scripts/run_graph.py` is intentionally minimal (~250 lines, no scheduler, no CAS, no caching). A passing `validate-outputs` diff attributes correctness to the *graph extractor*, not to executor cleverness. The executor is a regression-check tool, not part of the runtime distributed build.

---

## 6. Limitations

- **macOS-only constants**: the toolchain config (cc flags, link rsp tail) currently reflects Darwin. Linux/Windows would need a re-capture or, better, would read all of these from Lake's `Workspace` config (which is what the Lake-side walker already does — the limitation is only on the Python validator's ability to compare against a reference build).
- **`mathlib_test_executable`** has 16k+ cc nodes once cc emission lands; not practical for routine `validate-outputs` runs.
- **No graph-level fingerprint**: a hash covering the inputs that determine graph *shape* (lakefiles, `lake-manifest.json`, `lean-toolchain`, source headers) would let consumers skip re-running `graph-extract` when nothing graph-affecting changed. Not implemented; for mathlib4 the payoff is small (full extraction takes ~44s).
- **`run_graph.py` is single-job sequential**: by design (correctness over speed). The runtime distributed-build path uses Lake's executor, not this reference.

---

## 7. Source-of-truth pointers

When extractor output drifts from Lake itself, these are the call sites to consult (line numbers from `/Users/chelo/mathlib4/lean4-src/`):

| Behaviour | Lake source |
|---|---|
| `lean` argv shape | `Lake/Build/Actions.lean:mkLeanModuleArgs` (pure helper) + `compileLeanModule` (wrapper) |
| Module input parsing | `Lake/Build/Module.lean:30-42` (`recFetchInput`) |
| Direct-import collection | `Lake/Build/Module.lean:55-63` (`recParseImports`) |
| Raw transitive imports | `Lake/Build/Module.lean:96-108` (`recComputeTransImports`) |
| importArts walk (flag-filtered) | `Lake/Build/Module.lean:222-255` (`fetchTransImportArts`) |
| Module artifact paths | `Lake/Build/ModuleArtifacts.lean` + `Lake/Build/Module.lean` |
| Exe build flow | `Lake/Build/Executable.lean` |
| cc compile/link argv | `Lake/Build/Actions.lean:mkCcCompileArgs`, `Lake/Build/Common.lean:mkLinkObjArgs` |
| rsp file format | `Lake/Build/Actions.lean:renderRspContents` |
| Toolchain flags | `Lake/Config/InstallPath.lean` |
| Lean name escaping | core `Lean.Name` parsing rules |
| Cache integration in build | `Lake/Build/Common.lean:459, 518` (`getArtifactsUsingCache?`, `saveArtifact`) |
| Native cache CLI | `Lake/CLI/Main.lean:383-650` (`lake cache get/put/add/stage`) |
