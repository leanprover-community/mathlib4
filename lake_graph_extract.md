# `lake_graph_extract` — static Lake build-graph extractor for mathlib4

Companion tool to [`lake_build_graph_analysis.md`](./lake_build_graph_analysis.md). The analysis doc establishes that mathlib4's Lake build is *statically reconstructible* (regime 1 in §11). This tool implements the construction described in §6, the three-layer validation in §7, and the lean_exe coverage in §3.6/§5.3.

The intended consumer is a worker-pool dispatch system (Bazel-RBE-shaped, or a custom CAS+queue): the tool emits a graph JSON whose nodes are hermetic enough to dispatch.

---

## 1. Files

```
scripts/lake_graph_extract.py    extractor + validators (single Python module)
scripts/run_graph.py             reference executor (intentionally minimal)
scripts/dag_traversal.py         (pre-existing) parallel DAG traversal — used as a library for lean --deps-json batching
```

All three are standalone Python 3.11+ scripts. Run them from the mathlib4 root.

---

## 2. Workspace assumptions (the preflight gates)

The tool refuses to operate unless the workspace is in regime 1 (analysis doc §11.1). The `preflight` subcommand encodes the §10.11 health check:

- `lake --version` agrees with `lean-toolchain` on the Lean version.
- No active package's lakefile contains `target`/`module_facet`/`library_facet`/`extern_lib`/`precompileModules` outside `proofwidgets` (whose JS extraDep is explicitly opaque).
- `lake setup-file` over a representative module from each lib reports `plugins=[]`/`dynlibs=[]`.

Active packages are read from `lake-manifest.json`, not by walking `.lake/packages/` — that filters out stale resolution residue like `lean4-cli` (which is shadowed by the active `Cli` package).

The captured workspace constants the tool depends on:

| Constant | Source | Where used |
|---|---|---|
| `LEAN_PATH` | `lake build -v` capture | every `lean_module` node's env |
| toolchain bin (`<root>/bin/lean`, `<root>/bin/clang`) | `lake env sh -c 'command -v lean'` | `lean_module` and `cc_*` nodes |
| `<root>/include`, `<root>/lib`, `<root>/lib/lean`, `<root>/lib/libc` | toolchain layout | cc compile/link argv |
| `MACOSX_DEPLOYMENT_TARGET=99.0` | Lake source `getMacOSXDeploymentEnv` | `cc_link` env |
| Static cc compile flags | observed `lake build -v autolabel` cc_compile argv | every `cc_compile` node |
| Static cc link rsp tail | `.rsp` files Lake leaves on disk | every `cc_link` node |

If the toolchain bumps, several of these (the cc flags especially) need to be re-captured. The validators will trip immediately on drift.

---

## 3. Subcommands

```
python3 scripts/lake_graph_extract.py <subcommand> ...
```

### 3.1 `preflight`

Run the §10.11 health check.

```
python3 scripts/lake_graph_extract.py preflight
```

Exit 0 if the workspace is in regime 1, non-zero otherwise. Prints the Lake/toolchain version, dynamic-feature scan summary, and per-package plugins/dynlibs spot-check.

### 3.2 `emit <module>`

Emit a single `lean_module` node summary as JSON to stdout. Diagnostic, not used in pipelines.

```
python3 scripts/lake_graph_extract.py emit Mathlib.Init
```

Each call invokes `lake setup-file` once (a few seconds).

### 3.3 `emit-graph <target> [-o file] [--deps {transitive,immediate}]`

Emit the build subgraph for a target.

```
python3 scripts/lake_graph_extract.py emit-graph Mathlib.Init -o /tmp/graph.json
python3 scripts/lake_graph_extract.py emit-graph autolabel    -o /tmp/autolabel.json
python3 scripts/lake_graph_extract.py emit-graph Mathlib      -o /tmp/full.json   # 8310+ nodes
python3 scripts/lake_graph_extract.py emit-graph Mathlib.Algebra.Group.Defs -o /tmp/g.json --deps immediate
```

The target may be:
- a Lean module name (`Mathlib.Init`, `Aesop.BaseM`, `Cache.Hashing`)
- a `lean_exe` name from mathlib's lakefile (`autolabel`, `cache`, `mk_all`, ...)

The graph is topo-ordered (leaves first) and written with `$WORKSPACE` / `$LAKE_HOME` / `$TOOLCHAIN` / `$TOOLCHAIN_ROOT` placeholders so it's portable across machines that share the same toolchain.

**`--deps` modes:**

- `transitive` *(default)* — every `lean_module` node's `graph_deps` lists every module in its `setup_json.importArts`. Redundant given importArts already enumerates them, but explicit.
- `immediate` — `graph_deps` lists only direct imports. The scheduler computes transitivity by walking edges. Typical reduction is ~10× on `sum(len(graph_deps))`; on a 84-node `Mathlib.Algebra.Group.Defs` graph the totals go from 1552 to 156.

**The mode only affects `graph_deps`.** `setup_json.importArts` and `inputs` always carry the full transitive set — `lean --setup` reads every transitive olean and the worker must stage them all for hermetic execution. `cc_compile`/`cc_link` deps are already minimal (a cc_compile depends on its lean_module; a cc_link depends on every cc_compile in the closure, all of which it directly consumes), so those nodes are unaffected.

The mode is recorded as `graph["deps_mode"]` at the top level so consumers can detect it. `run_graph.py`'s closure walk handles both modes uniformly (it BFSs over `graph_deps` recursively).

**`--full` flag:** by default `emit-graph` writes a *summary* form — each node's `inputs` list and `setup_json.importArts` dict are replaced by their lengths, so the file is small and human-readable. The full form is required by `run_graph.py` and by `validate-outputs`'s internal use; pass `--full` to emit it. `validate-outputs` always uses the full form internally regardless of CLI defaults.

### 3.4 `validate-commands <module>`

Byte-exact diff between the extracted command and `lake build -v`'s argv for a module.

```
python3 scripts/lake_graph_extract.py validate-commands Mathlib.Init
```

Destructive: deletes the module's artifacts before invoking `lake build -v` so Lake actually runs `lean` (not `Replayed`). The artifacts get recreated by Lake's rebuild.

### 3.5 `validate-setup <module>`

Diff the statically-derived `setup.json` content against `lake setup-file <module>`.

```
python3 scripts/lake_graph_extract.py validate-setup Mathlib.Init
```

Reports semantic equivalence (sort_keys diff) and, separately, byte equivalence. Lake's emission order isn't replicable without re-implementing `Lean.Json`, so byte equality is reported as advisory; semantic equality is the correctness criterion (see §6.4 below).

### 3.6 `validate-outputs <target> [--full]`

End-to-end byte-equivalence: emit graph → delete the target's outputs → run `run_graph.py` → hash the rebuilt outputs → diff against the pre-existing golden hashes.

```
python3 scripts/lake_graph_extract.py validate-outputs Mathlib.Init
python3 scripts/lake_graph_extract.py validate-outputs autolabel
python3 scripts/lake_graph_extract.py validate-outputs Mathlib.Init --full   # rebuild whole closure
```

Modes:
- **Default (single-target)**: deletes only the target node's outputs, runs `run_graph.py --missing` (so transitive deps stay golden), diffs.
- **`--full`**: deletes every node's outputs in the closure and rebuilds the whole thing. Slow — comparable to a clean `lake build`.

Excluded from the diff (per §7.2): `*.hash`, `*.trace`, `*.rsp`, `*.setup.json`. Lake writes hash/trace sidecars with its own scheme that the reference executor doesn't replicate; the rsp file format is byte-equivalent for the same arg list (verified separately for autolabel.rsp); setup.json byte-form depends on JSON emission order (semantic equivalence is verified by `validate-setup` and `lean --setup` reads it semantically, so all downstream artifacts reproduce byte-exactly anyway).

### 3.7 `run_graph.py <graph.json> [--target ...] [--only|--missing|--clean]`

The reference executor.

```
python3 scripts/run_graph.py /tmp/graph.json
python3 scripts/run_graph.py /tmp/graph.json --target Mathlib.Init --only
python3 scripts/run_graph.py /tmp/graph.json --missing
python3 scripts/run_graph.py /tmp/graph.json --clean   # rm -rf .lake/build trees first
```

Flags:
- `--target`: restrict execution to a node id, exe name, or module name. Default: the graph's `target` field.
- `--only`: execute *only* the resolved target node, skipping its build deps. Useful for one-shot validation.
- `--missing`: execute only nodes whose declared outputs aren't already present. The validate-outputs single-target mode uses this to skip already-built transitive deps.
- `--clean`: `rm -rf` every `.lake/build` tree referenced by any node before executing. Required if the spec-strict §7.2 protocol is desired.

The executor is intentionally minimal: ~200 lines, no scheduler, no CAS, no caching. A passing `validate-outputs` diff attributes correctness to the *graph extractor*, not to executor cleverness.

---

## 4. Architecture

### 4.1 Module registry

`build_module_registry(packages)` produces a dict `module_name -> ModuleEntry` covering every `.lean` source under mathlib + every active package (lake-manifest entries; stale dirs filtered).

`ModuleEntry` records:
- `name` — dotted module name (path-derived, e.g. `Mathlib.Init`)
- `src` — absolute path to the source file
- `pkg` — owning package (`mathlib` or an upstream name)
- `lib` — first segment of `name` (Lake convention for default roots, holds for every lean_lib in the workspace today)
- `is_module` — module-style file? from `lean --deps-json` `isModule` field
- `imports` — list of `ImportEdge` carrying `module`, `is_exported`, `is_meta`, `import_all` (raw deps-json edges, deduped on the 4-tuple)

Imports are read in one batch via `lake env lean --deps-json --stdin` over every source path. This is the same primitive `scripts/dag_traversal.py` already uses; we extend the input set to include upstream packages.

### 4.2 Two transitive-imports walks

Lake distinguishes between "transitive imports" (used for collecting object files) and "import arts" (the `setup.json` field). They have different filtering rules. We mirror both:

- `transitive_imports(M)` — mirrors `Lake.Build.Module.fetchTransImportArts` (Lake/Build/Module.lean ~line 222). Filters edges by `imp.is_exported || importAll`; tracks the strongest importAll seen per module so a later visit can promote a 3-art entry to a 4-art entry; collapses non-module-style importers to importAll-everywhere via Lake's `nonModule` flag. Output: ordered list of modules + per-module importAll. Used to populate `setup.json.importArts`.
- `raw_transitive_imports(M)` — mirrors `Lake.Build.Module.recComputeTransImports`. No flag filtering; module-name dedup (matching Lake's `recParseImports`); post-order DFS. Used to enumerate cc_compile node objects for cc_link.

### 4.3 setup.json derivation

`derive_setup_json(M)` composes:

```json
{
  "name": <Lean-name-quoted M>,
  "package": <owning package>,
  "isModule": <from registry>,
  "options": <per-lib options from lake setup-file (cached)>,
  "plugins": [],
  "dynlibs": [],
  "importArts": { trans_dep: [olean, ir, olean.server (, olean.private)], ... }
}
```

- The `name` field uses `lean_name_repr`: any segment that isn't a valid Lean identifier (e.g. `check-yaml`) is wrapped in `«...»` to match Lake's serialization.
- `options` are read once per `(package, lib)` pair via `lake setup-file` on a representative source, then cached. Mathlib's libs without explicit `leanOptions` (Cache, MathlibTest, docs) get the canonical options Lake assigns at workspace level.
- `importArts` paths are 1, 3, or 4 elements based on Lake's encoding (Lake/Build/Module.lean comment at line 237):
  - 1 (`[olean]`) — imported file is non-module-style.
  - 3 (`[olean, ir, olean.server]`) — module-style, importAll false.
  - 4 (`[olean, ir, olean.server, olean.private]`) — module-style, importAll true.
- Plugins and dynlibs are forced empty per the preflight invariant.

### 4.4 lean_module nodes

`_build_lean_module_node_dict(M)` produces:

```json
{
  "id": "<pkg>:<module>",
  "kind": "lean_module",
  "module": <module name>,
  "package": <pkg>,
  "command": ["$TOOLCHAIN/lean", "$WORKSPACE/.../M.lean", "-o", ..., "-i", ..., "-c", ..., "--setup", ..., "--json"],
  "env": {"LEAN_PATH": <workspace-static colon-joined>},
  "inputs": [{"path": ..., "kind": "source"|"setup_json"|"import_art"}],
  "outputs": [".../olean", ".../ilean", ".../olean.server", ".../olean.private", ".../ir", ".../c", ".../setup.json"],
  "setup_json": { ... },
  "graph_deps": [<every transitive-import module name>]
}
```

Outputs depend on `is_module` — non-module files only emit `.olean`, `.ilean`, `.c`. The `setup.json` file is listed as both an input (read by `lean --setup`) and an output (written by the executor before invocation).

### 4.5 lean_exe nodes (three per exe)

For a `lean_exe` target, three node kinds get emitted in addition to the lean_module closure:

1. **lean_module node for the exe's root** — a special variant where Lake sees the source under a `srcDir` like `scripts/` but still calls the module by the bare `lean_exe` name (e.g. `scripts/autolabel.lean` → module name `autolabel`). The output paths use the bare name. `setup.json.options` is empty for these (the exe has no associated lean_lib).
2. **`cc_compile` per module in the closure** — `cc -c -o <stem>.c.o.export <stem>.c -I <toolchain>/include <static-flags> -DLEAN_EXPORTING`. Identical template across every module; only the source/output paths vary.
3. **`cc_link`** — `cc -o <bin> @<rsp>` with `MACOSX_DEPLOYMENT_TARGET=99.0`. The `.rsp` file content is computed statically: `[c.o.export files in raw-trans-imports order] ++ weakLinkArgs ++ [-L $TOOLCHAIN_ROOT/lib/lean] ++ <static link tail>`. The executor writes the `.rsp` to disk in Lake's quoted-line format (one quoted arg per line, backslash-escape `\` and `"`) before invoking cc.

The `cc_link.rsp_args` list and `cc_link.rsp_path` are first-class fields on the node (the rsp is *not* in the JSON encoding of the `command`, so the executor materializes it from these fields).

The exe-specific configs (root, srcDir, supportInterpreter, weakLinkArgs) are encoded as a static `LEAN_EXES` table in the script. This mirrors mathlib's lakefile.lean 1:1 today; if the lakefile changes, `validate-commands`/`validate-outputs` will trip immediately.

### 4.6 LEAN_PATH

Workspace-static. Empirically captured order: `Cli, batteries, Qq, aesop, proofwidgets, importGraph, LeanSearchClient, plausible, mathlib`. Every `lean_module` node carries the same `LEAN_PATH` string. If a package is added/removed/reordered, the captured list (`LEAN_PATH_PACKAGES` in the script) needs updating; `validate-commands` will trip on drift.

### 4.7 Path placeholders

The graph JSON uses POSIX-style placeholder paths so it's portable:

| Placeholder | Substitutes |
|---|---|
| `$WORKSPACE` | mathlib4 root |
| `$LAKE_HOME` | `$WORKSPACE/.lake` |
| `$TOOLCHAIN` | `<toolchain>/bin` (lean, clang) |
| `$TOOLCHAIN_ROOT` | `<toolchain>` (sysroot) |

Order of resolution is most-specific first (`LAKE_HOME` matches before `WORKSPACE`; `TOOLCHAIN` matches before `TOOLCHAIN_ROOT`). The `@<path>` rsp-arg form is handled specially: the `@` is preserved, the path part is relativized.

The `workspace` field of the graph JSON records the absolute paths the placeholders should resolve to on the emitter's machine; a worker on a different machine can override these and re-absolutize on its end.

---

## 5. Graph JSON schema

```json
{
  "version": "v1",
  "target": "Mathlib.Init",
  "deps_mode": "transitive"|"immediate",
  "workspace": {
    "WORKSPACE": "/Users/chelo/mathlib4",
    "LAKE_HOME": "/Users/chelo/mathlib4/.lake",
    "TOOLCHAIN": "/Users/chelo/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin",
    "TOOLCHAIN_ROOT": "/Users/chelo/.elan/toolchains/leanprover--lean4---v4.30.0-rc2"
  },
  "node_count": 56,
  "nodes": [
    {
      "id": "<pkg>:<module>",                 // or "<pkg>:cc_compile:<m>", "<pkg>:cc_link:<exe>", "<pkg>:exe:<exe>:lean"
      "kind": "lean_module"|"cc_compile"|"cc_link",
      "command": ["...", "..."],
      "env": {"...": "..."},
      "inputs": [{"path": "...", "kind": "source"|"setup_json"|"import_art"|"c_source"|"obj"|"response_file", "module": "..."}],
      "outputs": ["...", "..."],
      "graph_deps": ["..."],

      // lean_module only:
      "module": "...",
      "package": "...",
      "setup_json": { ... },

      // cc_compile only:
      "module": "...",
      "package": "...",

      // cc_link only:
      "exe_name": "...",
      "rsp_path": "...",
      "rsp_args": ["..."]
    }
  ]
}
```

Nodes are emitted in topological order (build deps before dependents). `graph_deps` may contain either node ids (for cc nodes) or module names (for lean_module nodes — these match Lake's `setup_json.importArts` keys).

---

## 6. Validation strategy (the three layers)

Each layer pins down a different correctness property; passing one does not subsume another.

### 6.1 `validate-commands` — extractor's argv ↔ Lake's argv

Byte-exact diff over `(env, argv)`. Catches drift in:
- LEAN_PATH order or contents (e.g. a package added to lakefile)
- output path conventions (e.g. Lake adding `.bc` for the LLVM backend)
- per-lib `leanArgs`/`weakLeanArgs` going non-static

Status: **9/9 modules pass** across mathlib, batteries, aesop, Cache; including widget-using files and the deepest mid-stack modules tested.

### 6.2 `validate-setup` — extractor's setup.json ↔ Lake's setup.json

Semantic JSON diff. Catches drift in:
- transitive-import filter rules
- per-lib options propagation
- `isModule`/`plugins`/`dynlibs` flags
- the size-1/3/4 art-shape selection

Status: **9/9 modules + Mathlib root (8310 importArts) pass** semantic equivalence. Byte equivalence is not enforced (Lake's emission order is implementation-defined).

### 6.3 `validate-outputs` — extracted graph reproduces Lake's artifact bytes

Per the §7.2 protocol. Hashes the artifacts a clean `lake build` would produce and the artifacts the extracted graph produces; diffs the manifests.

Status:
- **9/9 lean_module targets** byte-exact (leaf, mid-stack, deep, cross-package, non-module-style).
- **7/8 lean_exes** byte-exact (autolabel, cache, check-yaml, mk_all, lint-style, check_title_labels, nightly-testing-checklist). `mathlib_test_executable` deferred — investigation pending.
- Excluded files (documented above): `*.hash`, `*.trace`, `*.rsp` (matches anyway, not enforced), `*.setup.json` (semantic-only, see §6.4).

The standard form runs in single-target mode (delete + rebuild only the target's own outputs, transitive deps assumed golden). The `--full` form rebuilds the whole closure; useful for nightly cadence.

### 6.4 The setup.json byte-form caveat

Lake's `Lean.Json` writes setup.json with implementation-defined field/dict ordering. Our derivation produces semantically equivalent content with Python's json module's ordering. Byte forms differ; downstream artifacts (`.olean` etc.) are byte-identical because `lean --setup` parses semantically. `validate-outputs` excludes setup.json from the diff; `validate-setup` covers it via semantic comparison.

---

## 7. Known limitations / caveats

- **macOS-only constants**: `MACOSX_DEPLOYMENT_TARGET=99.0`, the static cc flag list, and the link rsp tail were captured on Darwin/x86_64. Linux/Windows would need a re-capture (the cc flag set differs and the link tail may use `-no-pie` etc.).
- **`mathlib_test_executable` validation is huge** (16,645 nodes — its closure is essentially all of mathlib + every package). A `--missing` rebuild from scratch produces ~14,000 cc_compile invocations and runs for many hours; not practical for routine validation. The original failure of this exe under `validate-outputs` traced to a deletion-collision bug (now fixed): the lean_module deletion used a stem-prefix sweep that wiped neighboring nodes' artifacts (`Mathlib.Init`'s lean_module deletion would also remove `Mathlib/Init.c.o.export`, which belongs to the cc_compile node). Per-node deletion now only touches each node's declared `outputs` plus immediate `.hash` / `.trace` sidecars.
- **Shared lakefile knowledge**: the `LEAN_EXES` table and `LEAN_PATH_PACKAGES` order are hand-mirrored from the lakefile rather than parsed. They match today; a lakefile edit would require updating the script too. The validators trip on any drift.
- **`lake setup-file` calls during emission**: per-lib `leanOptions` come from one `lake setup-file` per `(pkg, lib)`. For 10–15 lib pairs that's a few seconds each; cached so it pays once per `emit-graph` call.
- **Per-input sha256 not yet emitted**: input entries currently carry only `path`. Distributed dispatch needs `sha256` per input plus a per-node `cache_key`; see §8.
- **proofwidgets JS extraDep not modelled**: the `widgetPackageLock`/`widgetJsAll` targets in `proofwidgets/lakefile.lean` need to be a single opaque `package_extra_dep` node (analysis doc §10.4). Currently absent.
- **No graph-level fingerprint**: §12.1 covers what to fingerprint; not yet implemented.
- **`run_graph.py` is single-job sequential**: by design (correctness over speed). A real distributed dispatcher reads the same JSON.

---

## 8. Remaining work

In rough payoff order. Each item is independent.

### 8.1 `workspace_manifest.json` + per-input `sha256` + per-node `cache_key`

What §15 calls for: every input is `{path, sha256}`; the cache key is `sha256(normalized_command + sorted(env) + sorted(input.sha256))`. Adds a CAS-ready structure to the graph. Mostly mechanical:

- `workspace_manifest.json`: list of all source `.lean` paths with content sha256. Walks the same set the registry uses; one pass.
- Per-node input hashing: lazy + cached across nodes (most artifacts appear as inputs to many downstream nodes; hash once).
- `setup.json` is special — its content hash must be derived from the emitted JSON content (not from a non-existent on-disk file). Use canonical JSON dump (sort_keys, compact separators) for hash stability.
- `cache_key` follows directly.

Touches `_build_lean_module_node_dict`, `_build_cc_compile_node`, `_build_cc_link_node`, plus a new top-level emit for `workspace_manifest.json`. ~150 LoC.

### 8.2 proofwidgets opaque `package_extra_dep` node

A single node representing the curl + untar of proofwidgets' pre-built JS. Inputs: `lakefile.lean` (its hash gates the version), the URL/sha pinned in the lock file. Outputs: the JS tree under `.lake/packages/proofwidgets/.lake/build/js/`.

The node doesn't decompose; it executes whatever the proofwidgets `widgetPackageLock` target does. For our purposes this is a sealed-box: the worker fetches the JS once per package version. ~50 LoC.

### 8.3 Diagnose `mathlib_test_executable` validate-outputs

7/8 lean_exes pass; this one timed out after 30+min in a background run. The exe root is `MathlibTest/MathlibTestExecutable.lean`, which imports `Lean`/`Std`/`Qq` — so its raw transitive closure is huge but still finite. Possible causes:
- `lake setup-file` on this specific source happens to be unusually slow (deep import tree triggers heavy elaboration on the lake side?)
- The cc_link rsp ends up containing thousands of object paths, hitting some timeout in our validator
- A bug in `raw_transitive_imports` for a particular import shape this file uses

First step: time `lake setup-file MathlibTest/MathlibTestExecutable.lean` directly. If that's the bottleneck, the v1 oracle approach is unavoidable for this case; a workaround is to swap to derived setup.json for the exe-lean node too (we already do this for regular modules).

### 8.4 Optional `graph_fingerprint`

§12.1 of the analysis doc. A hash covering the inputs that determined graph *shape* (lakefiles tree-wide, `lake-manifest.json`, `lean-toolchain`, header prefixes of every source, Lake CLI flags, Lake binary itself). Would let consumers skip re-running `emit-graph` when nothing graph-affecting changed.

For mathlib4 today the payoff is small (graph construction takes ~5s for the deepest target, ~30s for the whole project). The real caching value sits at the node level, which is already covered by `cache_key` in §8.1.

### 8.5 Whole-project `emit-graph`

`emit-graph Mathlib` already produces 8310+ lean_module nodes. To produce the *true* "everything mathlib builds" graph (every lean_lib root + every lean_exe), we'd union the transitive closures. Mostly a CLI / orchestration item — the underlying emitters already work. ~30 LoC.

### 8.6 Spec-strict `validate-outputs`

The §7.2 protocol uses `lake build --no-cache` to establish the baseline rather than the existing cache. We use the cache as a stand-in (justified by independently-verified bit-reproducibility). Adding `--lake-baseline` to invoke the spec form for nightly runs would close the last gap. ~50 LoC.

### 8.7 Toolchain-portability

The captured cc flags and link rsp tail are macOS-specific. Adding a Linux capture path (read `lean.ccFlags` from `Lake.Config.InstallPath` at runtime, or capture once via a sample build per platform) would let the same extractor target Linux workers. Probably one afternoon's work but requires a Linux toolchain for capture.

---

## 9. Source-of-truth pointers

When something in this tool drifts from Lake itself, these are the call sites to consult:

| Behavior | Lake source |
|---|---|
| `lean` argv shape | `Lake/Build/Actions.lean:28-100` (`compileLeanModule`) |
| Module input parsing | `Lake/Build/Module.lean:30-38` |
| Direct-import collection | `Lake/Build/Module.lean:54-59` (`recParseImports`) |
| Raw transitive imports | `Lake/Build/Module.lean:96-104` (`recComputeTransImports`) |
| importArts walk | `Lake/Build/Module.lean:222-255` (`fetchTransImportArts`) |
| Module artifact paths | `Lake/Build/ModuleArtifacts.lean` + `Lake/Build/Module.lean:762-767` |
| Exe build flow | `Lake/Build/Executable.lean:22-54` |
| cc compile (object) | `Lake/Build/Actions.lean:101-109` (`compileO`) + `Common.lean:841-855` (`buildLeanO`) |
| cc link (exe) | `Lake/Build/Actions.lean:160-168` (`compileExe`) + `Common.lean:954-970` (`buildLeanExe`) |
| rsp file format | `Lake/Build/Actions.lean:111-125` (`mkArgs`) |
| Toolchain flags | `Lake/Config/InstallPath.lean:116, 274-279` |
| Lean name escaping | Lean core `Lean.Name` parsing (any segment failing identifier rules → `«...»`) |
