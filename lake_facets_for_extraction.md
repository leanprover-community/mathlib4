# Lake facet purity reference

For static graph extraction, only a small subset of Lake's facets is *evaluation-pure* — the result is a function of source headers and the lakefile, and no `lean` or `cc` invocation is triggered. Anything outside this subset will silently start compiles when fetched, even if its `buildable` flag is `false`.

This doc enumerates the boundary. The `lake graph-extract` walker (`Lake/Build/GraphExtract.lean`) operates strictly inside it.

---

## 1. The hard rule

Use only facets whose entire compute tree is pure on the import graph and the lakefile. The walker must remain runnable on a clean `.lake/build/` without warming any artifact.

This rules out anything that touches `:setup`, `:importArts`, `:exportInfo`, `:olean`, or any artifact-bearing facet — even though some of them are formally `buildable := false`, their *evaluation* awaits jobs that produce real artifacts. Empirically: `lake query +X:setup` triggered 277 module builds in our test run.

**The `buildable` flag is not a reliable purity signal. The transitive call graph is.**

---

## 2. Pure facets

The 28 module facets in `Module.initFacetConfigs` (`Lake/Build/Module.lean:1179-1209`) split into pure and impure. The pure subset:

| Facet | Returns | Compute body | Source |
|---|---|---|---|
| `:lean` | source path | `mod.input.fetch.map (·.path)` | `Module.lean:45-47` |
| `:input` | `{path, header, imports, trace}` | `recFetchInput`: `IO.FS.readFile` + `Lean.parseImports'` | `Module.lean:30-42` |
| `:header` | parsed `ModuleHeader` (`isModule`, `imports[]` with full flags) | `mod.input.fetch.map (·.header)` | `Module.lean:50-52` |
| `:imports` | direct local imports as `Array Module` | `recParseImports`: filter `input.imports` to local | `Module.lean:55-63` |
| `:transImports` | transitive imports as `Array Module` | `recComputeTransImports`: DFS over `:imports` | `Module.lean:96-108` |
| `:precompileImports` | transitive precompile imports | `recComputePrecompileImports` | `Module.lean:120-125` |

Each compute body bottoms out at `recFetchInput`, which only reads source headers. No fetch of artifact-bearing data. Empirically: `lake query +Mathlib.Algebra.Group.Basic:transImports` returns 272 entries in 0.6s on a cold cache, almost all of which is Lake startup.

---

## 3. Impure facets — do not use

| Facet | Why it builds |
|---|---|
| `:importInfo` | Calls `imp.exportInfo.fetch` per import (`Module.lean:423`) — exportInfo builds |
| `:exportInfo` | Calls `mod.leanArts.fetch` (`Module.lean:436`) — leanArts runs `lean` |
| `:importArts` | Derived from `:exportInfo` |
| `:importAllArts` | Derived from `:exportInfo` |
| `:setup` | Fetches extraDep + importInfo + dynlibs + plugins — multiple build paths |
| `:leanArts`, `:olean`, `:olean.server`, `:olean.private`, `:ilean`, `:ir`, `:c`, `:bc` | Run `lean` |
| `:co`, `:co.export`, `:co.noexport`, `:bco`, `:o`, `:o.export`, `:o.noexport` | Run `cc` |
| `:dynlib` | Run `cc` link |
| `:ltar` | Pack archive |

`exportInfoFacet` carries `buildable := false` — that means "not a top-level CLI build target," not "doesn't compile." Its compute body still triggers builds.

---

## 4. Library / package / exe facets

The same `buildable=false-but-actually-builds` pattern applies to library and exe facets (`:modules`, `:static`, `:shared`, `:exe`). None are usable under the hard rule.

Library and exe metadata that the walker needs (`leanOptions`, `roots`, `srcDir`, `supportInterpreter`, `weakLinkArgs`) lives on `LeanLibConfig` / `LeanExeConfig` and is accessible directly through Lake's elaborated `Workspace` after lakefile load — no facet query required.

```lean
for lib in workspace.leanLibs do
  let opts   := lib.leanOptions          -- Array LeanOption, the lakefile's literal
  let roots  := lib.config.roots         -- Array Name
  ...

for exe in workspace.leanExes do
  let root   := exe.root
  let srcDir := exe.config.srcDir
  ...
```

These reads are pure on the elaborated lakefile — they don't go through Lake's `Job` machinery, so they don't trigger builds. Anything dynamic that *was* in the lakefile has already been resolved by the time the walker runs.

---

## 5. Where the walker still hand-mirrors Lake

A small set of derivations still mirror Lake source rather than driving Lake directly. Each is mitigated by a regression validator (see `lake_graph_extract.md` §5).

### 5.1 `fetchTransImportArts` flag-filter walk

Reconstructing `setup.json.importArts` requires the flag-filtered transitive walk: filter on `isExported || importAll`, track strongest `importAll` per module, collapse non-module-style importers via the `nonModule` flag. The pure-facet substitute would be `:importArts`, which is impure.

The walker mirrors `fetchTransImportArts`'s logic (`Lake/Build/Module.lean:222-255`). `validate-setup` is the oracle: any change to Lake's filter rules trips it on the next CI run.

### 5.2 Path conventions

`<lib_root>.olean`, `<ir_root>.c`, the 1/3/4-element importArts size lattice, the `lean -o ... -i ... -c ... --setup ... --json` argv shape — these aren't graph data, they're Lake's output conventions, set in `Lake/Build/Actions.lean` and `Lake/Build/ModuleArtifacts.lean`. No facet exposes them.

`mkLeanModuleArgs` (the public helper in `Lake/Build/Actions.lean`) is now the source of truth for the argv; the walker calls it directly. Path conventions for the artifact files themselves are still string-templated.

### 5.3 cc compile/link templates

For `cc_compile` / `cc_link` nodes (not yet emitted by the walker — see handoff doc), the cc flag list and link rsp tail come from `ws.lakeEnv.lean.{ccFlags, ccLinkFlags}` plus `mkCcCompileArgs` / `mkLinkObjArgs` (public helpers). No empirical capture per platform; the walker just reads what Lake itself would use.

### 5.4 LEAN_PATH

Read from `ws.augmentedLeanPath` directly. No hand-curated package-order table.

---

## 6. Source-of-truth pointers

| Topic | Source |
|---|---|
| Pure facet definitions | `Lake/Build/Module.lean:30-125` |
| Impure boundary (`exportInfo`, `importInfo`) | `Lake/Build/Module.lean:419-479` |
| Module facet registry | `Lake/Build/Module.lean:1179-1209` |
| `FacetConfig` / `ModuleFacetConfig` | `Lake/Config/FacetConfig.lean:15-77` |
| Workspace facet config storage | `Lake/Config/Workspace.lean:51, 257-262` |
| `lake query` CLI | `Lake/CLI/Build.lean:37-77`; `Lake/CLI/Help.lean:168-180` |
| Per-lib `LeanLibConfig.leanOptions` | `Lake/Config/LeanLibConfig.lean` |
| Per-exe `LeanExeConfig` | `Lake/Config/LeanExeConfig.lean` |
| Cache integration in build | `Lake/Build/Common.lean:459, 518` |
