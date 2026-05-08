# Can mathlib4's Lake build be represented as a fully static (command, inputs, outputs) graph?

**Verdict: ⚠️ Partially static — effectively fully static for mathlib4.**

The Lake build graph for mathlib4 can be reconstructed ahead of execution with very high fidelity. Lake itself permits arbitrary Lean computation in build definitions, but mathlib4 demonstrably does not use that capability. The per-module `lean` command is uniform; all per-module variability lives in a JSON "setup file" whose contents are derivable from the lakefile + the import graph + fixed path conventions.

Target representation:

```
Node = { command: string, inputs: set[Path], outputs: set[Path] }
```

All three fields are computable statically for every module, every `lean_exe`, and their linked artifacts in mathlib4.

**Ultimate goal driving this analysis: distributed execution.** The motivation for extracting a graph is to dispatch mathlib's build across a worker pool (Bazel-style remote execution, custom queue + CAS, etc.). The criteria that follow from that — full enumeration before dispatch, node-level hermeticity, content-addressed inputs/outputs, deterministic commands — are covered in §13. The static-reconstruction work in §1–§9 is the pre-requisite; §10–§13 address what changes (or breaks) when the assumption of staticity weakens, and how to recover.

**Explicit correctness goal: observational equivalence with `lake build`.** Running the extracted graph in topological order (via a trivial local executor, no scheduler, no CAS) from a clean `.lake/build/` must produce byte-identical artifacts to invoking `lake build` on the same targets from the same clean state. This is the ground-truth check that the extractor has not silently dropped an input, mis-ordered `LEAN_PATH`, or missed a side-effect of Lake's build orchestration. It is stronger than command-level agreement (§7.1) because it catches hidden environmental state that can slip past byte-compare of command lines. Executable form in §7.2.

---

## 1. Environment (for reproducibility)

- Host: Darwin 25.4.0, macOS
- Lake: `Lake version 5.0.0-src+3dc1a08 (Lean version 4.30.0-rc2)`
- Toolchain: `leanprover/lean4:v4.30.0-rc2` (from `mathlib4/lean-toolchain`)
- Mathlib4: branch `master` at commit `d480e9ea56`
- Lake source: `/Users/chelo/lean4/src/lake/Lake/`
- Mathlib4 root: `/Users/chelo/mathlib4/`
- mathlib4 was pre-built (cache warm): `.lake/build/lib/lean/Mathlib/Init.olean` etc. exist.

All Bash commands below were run from `/Users/chelo/mathlib4/`.

---

## 2. `dag_traversal.py` — what it provides, what it lacks

File: `scripts/dag_traversal.py` (934 lines).

**What it does.** Parallel orchestrator over the **module-level import DAG**:

- `DAG.from_directories(project_root, [directories])` at line 532:
  - Walks `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/` by default (line 542).
  - Collects all `.lean` paths relative to project root.
  - Calls `_parse_all_imports` (line 467) which runs:
    ```
    lake env lean --deps-json --stdin
    ```
    with all paths on stdin and parses the resulting JSON.
- `ModuleInfo` (line 448): `{name, filepath, imports, importers}`. **No commands, no output paths, no non-module inputs.**
- `DAGTraverser.traverse` runs an action callable per module with critical-path priority scheduling.

**Relative to the target schema.**

| Target field | Present in `dag_traversal.py`? |
|---|---|
| `command` | ❌ not modelled |
| `inputs` | partial — imports of a module, but not transitive `.olean`s or setup file |
| `outputs` | ❌ not modelled |

**Soundness as a starting point.** The module-to-module edge set is isomorphic to Lake's actual dependency DAG for mathlib4 because mathlib uses neither `precompileModules` (which would add module→dynlib edges) nor per-module custom targets. See §4.

---

## 3. Lake's build model (source-level)

### 3.1 Where the `lean` invocation is constructed

`Lake/Build/Actions.lean:28-100` — `compileLeanModule`:

```lean
public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (leanir : FilePath := "leanir")
: LogIO Unit := do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then args := args ++ #["-i", ileanFile.toString]
  ...
  if let some cFile := arts.c? then args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then args := args ++ #["-b", bcFile.toString]
  IO.FS.writeFile setupFile (toJson setup).pretty
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  ...
  rawProc { args, cmd := lean.toString, env := #[("LEAN_PATH", leanPath.toString)] }
```

**Command shape** (empirically confirmed; see §5):

```
LEAN_PATH=<search path> lean <source.lean>
  -o <x.olean>  -i <x.ilean>  -c <x.c>  [-b <x.bc>]
  --setup <x.setup.json>  --json
  <leanArgs...>
```

### 3.2 `leanArgs` source

`Lake/Config/LeanLib.lean:189-197`: `leanArgs` = buildType args ++ package `moreLeanArgs` ++ library `moreLeanArgs`; `weakLeanArgs` = package `weakLeanArgs` ++ library `weakLeanArgs`. Assembled at `Build/Module.lean:~852`:

```lean
let args := mod.weakLeanArgs ++ mod.leanArgs
```

All sourced from static arrays declared in the lakefile. No Lean term is elaborated at build time to produce them.

### 3.3 `ModuleSetup` (what goes into the `--setup` JSON)

Schema observed empirically (see §5.2): `{ dynlibs, importArts, isModule, name, options, package, plugins }`.

- `options` — the lakefile's `leanOptions` serialised (keys like `pp.unicode.fun`, `autoImplicit`, weak linter options).
- `importArts` — `{ moduleName : [olean, ir, olean.server] }` for every transitive import.
- `plugins` — shared libraries to load via `--plugin`.
- `dynlibs` — shared libraries to load via `--load-dynlib` (populated when `precompileModules=true`).
- `isModule` — is this a `module`-style Lean file (affects which `.olean.*` outputs exist).

### 3.4 Import discovery is header-only (no elaboration)

`Lake/Build/Module.lean:30-38` — `Module.recFetchInput`:

```lean
let contents ← IO.FS.readFile path
...
let header ← Lean.parseImports' contents path.toString
let imports ← header.imports.mapM fun imp => do
  return ⟨imp, (← findModule? imp.module)⟩
```

`Lake/Build/Module.lean:96-108` — `recComputeTransImports` walks the parsed header graph.

This is exactly the information `lean --deps-json` provides; the graph is known before any `lean` invocation.

### 3.5 Outputs per module

`Lake/Build/ModuleArtifacts.lean:16-26` + `Build/Module.lean:762-767`:
- Mandatory: `.olean`, `.ilean`, `.c`.
- Module-style only: `.olean.server`, `.olean.private`, `.ir`.
- LLVM backend only: `.bc`.
- Archive: `.ltar` (optional).
- Paths follow `.lake/build/lib/lean/<Module>.{olean,ilean,olean.server,olean.private,ir,*.hash}` and `.lake/build/ir/<Module>.{c,setup.json,c.o.export,c.hash,...}`.

### 3.6 `lean_exe` build

`Lake/Build/Executable.lean:22-54` fetches transitive `.c.o.export` objects and calls:
- `compileExe` at `Actions.lean:160-168` — `cc -o <bin> @<bin.rsp>` with `MACOSX_DEPLOYMENT_TARGET` set.
- C objects are produced by `compileO` (`Actions.lean:101-109`) — `cc -c -o <x.c.o> <x.c> <moreArgs>`.

### 3.7 Other concerns

- **`post_update` hooks** (`Lake/Load/Resolve.lean:402-406`): run after build completes, do not affect the current build's DAG.
- **`extraDepTargets`** (`Lake/Config/{Package,LeanLib,LeanExe}Config.lean`): coarse-grained prerequisites; mathlib's package config does not set these.
- **`lake setup-file`** (`Lake/CLI/Serve.lean:43-85`): internal command used by the LSP; calls `ws.runBuild` around `setupServerModule` — it materialises the dep build before printing setup JSON. Useful for inspection but not a pure static extractor.

---

## 4. Does mathlib4 use Lake's dynamic features?

Direct reading of `/Users/chelo/mathlib4/lakefile.lean`:

| Feature | Used? | Notes |
|---|---|---|
| `leanOptions` | Yes | Static array `mathlibLeanOptions` (lines 42–47). |
| `moreLeanArgs`, `weakLeanArgs` | No | — |
| `precompileModules` | **No** | No module→dynlib edges added. |
| `extraDepTargets` | No | Package config does not set it. |
| Programmatically generated `lean_lib` roots | No | Globs are static (`#[\`Cache.+]`, etc.). |
| Custom module facets / custom targets | No | — |
| `post_update` | Yes | Lines 141–170, but runs *after* the build graph executes. |

Declared `lean_lib`s (lines 61–82): `Mathlib` (default_target), `Cache`, `MathlibTest`, `Archive`, `Counterexamples`, `docs`.
Declared `lean_exe`s (lines 95–131): `autolabel`, `cache`, `check-yaml`, `mk_all`, `lint-style`, `check_title_labels`, `nightly-testing-checklist`, `mathlib_test_executable`.

**All declarations are static.** The only non-mathlib dynamism is `proofwidgets`'s dependency-level `extraDep` which fetches pre-built JS — a package-level one-shot side effect, not a per-module concern.

---

## 5. Empirical results

### 5.1 Command shape for a fresh module build

A minimal scratch project reproduced in `/tmp/lake_test`:

```bash
cd /tmp && rm -rf lake_test && mkdir lake_test && cd lake_test
echo '-- test file' > A.lean
echo 'import A'     > B.lean
cat > lakefile.lean <<'EOF'
import Lake
open Lake DSL
package test
@[default_target]
lean_lib Test where
  roots := #[`A, `B]
EOF
echo "leanprover/lean4:v4.30.0-rc2" > lean-toolchain
lake build -v 2>&1 | head -30
```

Observed (relevant lines):

```
ℹ [2/4] Built A (149ms)
trace: .> LEAN_PATH=/private/tmp/lake_test/.lake/build/lib/lean \
  /Users/chelo/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean \
  /private/tmp/lake_test/A.lean \
  -o /private/tmp/lake_test/.lake/build/lib/lean/A.olean \
  -i /private/tmp/lake_test/.lake/build/lib/lean/A.ilean \
  -c /private/tmp/lake_test/.lake/build/ir/A.c \
  --setup /private/tmp/lake_test/.lake/build/ir/A.setup.json \
  --json
ℹ [3/4] Built B (149ms)
trace: .> LEAN_PATH=...  lean  B.lean  -o ...B.olean  -i ...B.ilean  -c ...B.c  \
       --setup ...B.setup.json  --json
```

Confirms the command template of §3.1 with per-module variability consisting entirely of `<source>` and output paths.

### 5.2 `lake setup-file` over three representative mathlib modules

```bash
# from /Users/chelo/mathlib4/
lake setup-file Mathlib/Init.lean              | python3 -m json.tool | head -20
lake setup-file Mathlib/Tactic/Widget/Calc.lean | python3 -m json.tool | head -20
lake setup-file Mathlib.lean                   | python3 -m json.tool | head -20
```

Summary (extracted programmatically):

| Module | `plugins` | `dynlibs` | `importArts` count | `isModule` |
|---|---|---|---|---|
| `Mathlib/Init.lean` | `[]` | `[]` | 54 | `True` |
| `Mathlib/Tactic/Widget/Calc.lean` | `[]` | `[]` | 66 | `True` |
| `Mathlib.lean` (root) | `[]` | `[]` | 8310 | `True` |

Options (same for all three):

```json
{
  "autoImplicit": false,
  "maxSynthPendingDepth": 3,
  "pp.unicode.fun": true,
  "weak.linter.allScriptsDocumented": true,
  "weak.linter.checkInitImports": true,
  "weak.linter.mathlibStandardSet": true,
  "weak.linter.pythonStyle": true,
  "weak.linter.style.header": true,
  "weak.linter.style.longFile": 1500
}
```

These match `mathlibLeanOptions` in `lakefile.lean:42-47` exactly. No plugins, no dynlibs, even on a widget-using module.

### 5.3 `lean_exe` command trio

```bash
lake build -v autolabel 2>&1 | grep '^trace: \.>'
```

Observed three commands (paths abbreviated):

1. `lean` invocation producing `.olean`, `.ilean`, `.c` (same template as §5.1).
2. `clang -c -o autolabel.c.o.export autolabel.c -I <lean-include> -fstack-clash-protection -fdata-sections -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument --sysroot <toolchain> -nostdinc -isystem <toolchain>/include/clang -O3 -DNDEBUG -DLEAN_EXPORTING` — flags are entirely static.
3. `MACOSX_DEPLOYMENT_TARGET=99.0 clang -o autolabel @autolabel.rsp` — `.rsp` file contains the transitive object list, which is determined by the import graph.

### 5.4 Import graph extraction cost (already measured by Lake and `dag_traversal.py`)

Both Lake (`Lake.parseImports'`) and `dag_traversal.py` (`lean --deps-json --stdin`) parse headers only — no elaboration. Total one-shot cost on mathlib: seconds, not minutes.

---

## 6. Static reconstruction recipe (concrete)

Inputs available ahead of build:
- `lakefile.lean` and all transitive packages' lakefiles.
- All `.lean` source files.
- `lean --deps-json` over all `.lean` files (from `dag_traversal.py`).
- Fixed path conventions (§3.5).

Per-module output node:

```
M = <module name, e.g. Mathlib.Algebra.Group.Basic>
src(M)         = "Mathlib/Algebra/Group/Basic.lean"
lib_root(M)    = ".lake/build/lib/lean/Mathlib/Algebra/Group/Basic"
ir_root(M)     = ".lake/build/ir/Mathlib/Algebra/Group/Basic"
trans(M)       = transitive-imports(M)  // from lean --deps-json graph walk

outputs(M) = {
  "<lib_root(M)>.olean",
  "<lib_root(M)>.ilean",
  "<lib_root(M)>.olean.server",    // isModule=true
  "<lib_root(M)>.olean.private",   // isModule=true
  "<lib_root(M)>.ir",              // isModule=true
  "<lib_root(M)>.olean.hash",
  "<lib_root(M)>.ilean.hash",
  "<ir_root(M)>.c",
  "<ir_root(M)>.setup.json",
  "<ir_root(M)>.c.o.export",       // if c.o target will be built
}

inputs(M) = {
  src(M),
  "<ir_root(M)>.setup.json",
  ∪_{t ∈ trans(M)} {
    "<lib_root_of(t)>.olean",
    "<lib_root_of(t)>.ir",
    "<lib_root_of(t)>.olean.server",
  }
}

env(M) = {
  "LEAN_PATH": ":".join(package_lib_dirs)   // static per workspace
}

command(M) = [
  "<lean>",
  src(M),
  "-o", "<lib_root(M)>.olean",
  "-i", "<lib_root(M)>.ilean",
  "-c", "<ir_root(M)>.c",
  "--setup", "<ir_root(M)>.setup.json",
  "--json",
  *leanArgs_for(lib_containing(M)),
]

setup_json(M) = {
  "name":    "<module-name>",
  "package": "<package-name>",
  "isModule": true,
  "options": <leanOptions from lakefile for M's lean_lib>,
  "plugins": [],
  "dynlibs": [],
  "importArts": { t: [olean(t), ir(t), olean_server(t)] for t ∈ trans(M) },
}
```

For `lean_exe` nodes, add:
- `compileO` node per transitive module (`cc -c -o <x.c.o.export> <x.c> <static flags>`).
- `compileExe` link node (`cc -o <bin> @<bin.rsp>` with static content).

**Assumptions, made explicit:**

- mathlib4 continues not to use `precompileModules`, custom targets, or non-static `leanArgs`. Violations are detectable by diffing setup JSON of a sample.
- `proofwidgets`'s JS `extraDep` is modelled as a coarse opaque node (fetch → unpack → produce JS tree) and is not decomposed.
- Cache restoration (`lake exe cache get`) is orthogonal: it replaces `lean` invocations with file downloads but does not change the graph's structure.

---

## 7. Validation plan

Two layers. §7.1 validates that the extractor's *descriptions* of work match Lake's. §7.2 validates that *actually doing* the work produces the same artifacts as Lake. Both are required; neither subsumes the other.

### 7.1 Command-level equivalence (extractor output ↔ Lake's intentions)

1. Generate static nodes for a sample of 20 modules with varying depth (leaves, mid-stack, `Mathlib.lean` root).
2. For each sampled module, run:
   ```
   lake build -v --no-cache <module> 2>&1 | grep '^trace: \.>'
   ```
3. Diff the observed `trace:` lines against the statically generated `command + env`. Expect byte-exact matches modulo ordering of `-o/-i/-c` flags.
4. For each sampled module, diff the static `setup_json(M)` against `cat .lake/build/ir/<module>.setup.json`.
5. Run `lake build -v autolabel --no-cache` and compare all three node types (lean, `cc -c`, `cc -o`).

Expected failure modes (actionable):

- If `trace:` shows a `--plugin` or `--load-dynlib` flag on any mathlib module, a package upstream has changed to emit dynlibs — rerun §5.2 scan.
- If `setup.json.options` drifts from the lakefile literal, a package has started injecting options via `moreServerOptions` — extract them from a representative `lake setup-file` call.

### 7.2 End-to-end output equivalence (executed graph ↔ Lake build)

This is the ground-truth check the project must pass before the extracted graph can be trusted for distributed execution.

**Protocol (per sampled target):**

```bash
# --- Baseline: Lake build from clean ---
rm -rf .lake/build
lake build --no-cache <target>
find .lake/build -type f \
  \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' \
     -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ir' \
     -o -name '*.c.o.export' \) \
  | sort | xargs sha256sum > /tmp/lake_outputs.txt

# --- Extracted graph, executed locally in topological order ---
rm -rf .lake/build
./run_graph.py build_graph.json --target <target> --jobs 1
find .lake/build -type f \
  \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' \
     -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ir' \
     -o -name '*.c.o.export' \) \
  | sort | xargs sha256sum > /tmp/graph_outputs.txt

diff /tmp/lake_outputs.txt /tmp/graph_outputs.txt
```

`run_graph.py` is a trivial reference executor that takes `build_graph.json`, topologically orders the reachable subgraph, and invokes each node's `command` with its `env` — nothing else. No CAS, no remote dispatch, no scheduling. Its whole job is to be *so simple* that a passing `diff` attributes correctness to the extractor, not to the executor.

**Targets to cover:**

- One leaf module (e.g., a file imported by nothing).
- One mid-stack module with ~100 transitive imports.
- One deep module (`Mathlib.lean` itself, or a near-root combinator).
- One `lean_exe` (`autolabel`) — exercises `cc_compile` + `cc_link` nodes.
- One `supportInterpreter=true` exe (e.g., `mk_all`) — different link flags.
- One module from each `lean_lib` (`Cache`, `MathlibTest`, `Archive`, `Counterexamples`) — catches per-lib `leanOptions` drift.

**What must match:**

- Set of output paths: identical.
- Content hashes of `.olean`, `.ilean`, `.c`, `.olean.server`, `.olean.private`, `.ir`, `.c.o.export`: bit-identical.

**What is allowed to differ (document explicitly):**

- `.rsp` response files: paths only, content is a deterministic function of the input list but format/ordering may vary harmlessly.
- `.hash`, `.trace` sidecar files: Lake writes these with its own hashing scheme; if the reference executor does not replicate the scheme, expect misses here. Either replicate Lake's hash format in the executor (preferred) or exclude from the diff (acceptable for v1).
- Build logs, mtimes.

**Expected failure modes:**

- Non-empty diff on `.olean` content → a genuine input is missing from the node's declared inputs (hermeticity bug). Investigate by re-running Lake with `strace`/`dtruss` to enumerate the real read set.
- Non-empty diff on `.c` content but matching `.olean` → backend-flag mismatch, or `setup.json.options` drift. Re-check §5.2.
- Lake succeeds but graph executor fails → `LEAN_PATH` order wrong, or a transitive dynlib/plugin missing. §10.1/§10.5 check is probably overdue.
- Graph executor succeeds but Lake fails → unlikely; suggests the extractor is loosening a constraint Lake enforces (e.g., running a node whose deps Lake would have refused to schedule).

**Scaling to full mathlib.** The per-module sample above catches regressions cheaply. A full-graph equivalence run (`rm -rf .lake/build; ./run_graph.py build_graph.json; diff`) is the definitive test but takes a full mathlib build's wall time. Run it in CI on a nightly cadence, or after any change to the extractor.

**Determinism caveat.** This protocol assumes Lean compilation is bit-reproducible given fixed inputs. The existence of `lake exe cache` (content-addressed olean distribution) is strong empirical evidence for this. If a module is discovered to be non-reproducible, the diff must be scoped to its transitive-input hash rather than its output content — which is a property a hermetic distributed build requires regardless.

---

## 8. Irreducible dynamism (bounded)

1. **Header parsing** to get transitive imports. One `lean --deps-json` batch over all `.lean` files. Unavoidable but cheap.
2. **proofwidgets `extraDep`** (curl + unpack of pre-built JS). One-shot per package version. Model as an opaque node.
3. **Cache restoration** (`lake exe cache get`). Same: file download rather than compilation, but does not alter the module DAG.
4. **Hash/trace sidecar files** (`*.hash`, `*.trace`). Deterministic from inputs; trivially modellable as outputs.

None of these require evaluating Lean code at graph-construction time for any mathlib4 node.

---

## 9. Instrumentation fallback (if static recipe proves insufficient)

If a future mathlib version adopts dynamic features, the cleanest point to capture the graph as-it's-constructed is in `Lake/Build/Module.lean`, immediately before `compileLeanModule` is invoked (around the site of `let args := mod.weakLeanArgs ++ mod.leanArgs`). At that point:

- `mod.leanFile`, `setup` (fully populated `ModuleSetup`), `arts : ModuleArtifacts`, `leanArgs`, `leanPath` are all in scope.
- Emit a JSON record `{module, command, env, inputs, outputs}` to a side file instead of (or in addition to) calling the subprocess.

A `LAKE_BUILD_GRAPH_OUT=<file>` env-gated emitter of ~15 lines of Lean at that call site suffices. Mirror the pattern at `compileO` (`Actions.lean:101`) and `compileExe` (`Actions.lean:160`) for non-Lean nodes.

---

## 10. Lake features that would make static extraction lossy or wrong

Ordered roughly by how likely they are to bite a real Lean project, with a specific guard for each.

### 10.1 `precompileModules := true` on a `lean_lib`

**Why it breaks.** Each imported module must be built as a `.dylib`/`.so` *before* its importers, and the importers' setup JSON gets a non-empty `dynlibs`/`plugins` list. The module-level DAG gains edges that are invisible in `lean --deps-json`, and the `lean` command may gain `--load-dynlib` flags.

**Guard.** After each `lake update` or toolchain bump:

```bash
grep -rn "precompileModules" lakefile.lean .lake/packages/*/lakefile.*
```

and confirm `setup.json` samples still have `dynlibs=[]` and `plugins=[]` (one `lake setup-file` call per `lean_lib`).

### 10.2 Custom `target` / `module_facet` / `library_facet` declarations in the lakefile

**Why it breaks.** Arbitrary Lean code runs in `FetchM` to produce outputs. Neither the command nor the inputs/outputs are inferable without executing the monadic build action.

**Guard.**

```bash
grep -En '^\s*(target|module_facet|library_facet|extern_lib)\b' lakefile.lean
```

Any match → fall back to the instrumentation approach in §9.

### 10.3 Non-static `moreLeanArgs`, `weakLeanArgs`, `moreServerOptions`

**Why it breaks.** These fields accept `do`-notation that can read env vars, files, or compute dynamically. Mathlib currently uses literal `#[...]` arrays, but an upstream package could change.

**Guard.** Compare `lake setup-file` on one representative module per `lean_lib` against the statically-derived expected value. Fail CI on drift.

### 10.4 `extraDepTargets` that point to non-trivial custom targets

**Why it breaks.** These run before module builds and can produce generated `.lean` files (common pattern: protobuf-like codegen). If a file under `Mathlib/` is *generated*, `lean --deps-json` won't see it before extraDep runs, so the import graph is incomplete.

**Guard.** After running `lake build :extraDep` for each package, diff the set of `.lean` files against the pre-build set:

```bash
find Mathlib -name '*.lean' | sort > before.txt
lake build :extraDep
find Mathlib -name '*.lean' | sort > after.txt
diff before.txt after.txt  # must be empty
```

### 10.5 `load_dynlib` / `lean_plugin` declarations pulled in by upstream packages

**Why it breaks.** `plugins` becomes non-empty, the `lean` command gains `--plugin=...`, and the dynlib itself becomes a build-graph node whose command (`cc -shared` with arbitrary link args) is non-uniform.

**Guard.** The §10.1 check catches this — any module with `setup.json.plugins != []` means the plugin's build must be modelled.

### 10.6 `supportInterpreter := true` on a `lean_exe`

**Why it breaks.** The exe links the Lean interpreter and thus `-lLake`, `-lLean`, etc., so the `cc -o` step's `.rsp` contents and link flags shift. Mathlib uses this on `check-yaml`, `mk_all`, `lint-style` (lakefile lines 105, 110, 117).

**Guard.** Deterministic, but the extractor must branch on `config.supportInterpreter` and propagate `weakLinkArgs` verbatim. Assert by running the validation sub-command (§7) on at least one `supportInterpreter` exe.

### 10.7 `post_update` hooks that write files in the workspace

**Why it breaks.** Mathlib's own `post_update` runs `lake exe cache` which writes `.olean`s. Edges are unaffected, but "does this output exist yet?" becomes answer-dependent on whether the hook has fired.

**Guard.** Either run the extractor only from a clean `.lake/build/`, or treat `.olean` outputs as "expected but may pre-exist from cache". Don't rely on mtimes.

### 10.8 `require ... from ...` path dependencies with their own custom lakefiles

**Why it breaks.** A sibling package outside mathlib's review could use any of features 10.1–10.6. Static extraction is only as sound as the weakest upstream lakefile.

**Guard.** Run §10.1, §10.2, §10.5 checks over *every* `.lake/packages/*/lakefile.*`, not just mathlib's. Script it and run in CI.

### 10.9 Lake option overrides via `-K key=value`

**Why it breaks.** `-K` can flip `buildType`, which changes the auto-derived parts of `leanArgs`. The command line changes without any source file changing.

**Guard.** The extractor takes the same `-K` flags as input (or pins `buildType := .release`) and records them in the node JSON.

### 10.10 Toolchain mismatch between `lean-toolchain` and the `lake` binary on PATH

**Why it breaks.** Path conventions (e.g. `olean.server` existence, default flags) have shifted across Lean 4 versions. An extractor pinned to v4.30.0-rc2 conventions will mis-predict on v4.29 or v4.31.

**Guard.** The extractor refuses to run if `lake --version`'s Lean version ≠ `lean-toolchain`, and is re-validated whenever the toolchain bumps.

### 10.11 Combined "health check"

Run this before trusting a generated graph:

```bash
# in repo root
lake --version
grep -rn -E '^\s*(target|module_facet|library_facet|extern_lib|precompileModules)\b' \
  lakefile.lean .lake/packages/*/lakefile.*
for lib in Mathlib Cache MathlibTest Archive Counterexamples; do
  # pick one module per lib, run setup-file, assert plugins=[] dynlibs=[]
  ...
done
```

All three green → static reconstruction is sound. Any red → fall back to the instrumentation in §9.

---

## 11. Three dynamism regimes (and which one mathlib is in)

The question "can Lake's build graph be reconstructed statically?" decomposes into three regimes, distinguished by *when* graph information becomes available.

### 11.1 Statically reconstructible

Graph = pure function of source files + lakefile configuration. No build execution is required to know the graph. Fingerprint = hash of source files + lakefile contents + toolchain.

**Mathlib4 is in this regime** (evidence: §4, §5).

### 11.2 Lakefile-elaboration dynamic

The lakefile contains arbitrary Lean code (reads env vars, shells out to `git`, iterates directories, etc.) but only consumes *source* and *config* — nothing produced by earlier build steps. Elaborating the lakefile to compute the graph costs a few seconds even for a large project. Still orders of magnitude cheaper than actually compiling modules. Fingerprint must additionally cover env vars and any files the lakefile reads.

### 11.3 Build-output dynamic

A node's command/inputs/outputs depend on the *contents* of another node's *output files*. Canonical example: a codegen target whose generated `.lean` files are then imported downstream — you cannot know downstream modules' transitive imports until codegen has run. In Lake, any custom `target` defined via `FetchM` is *capable* of this: `await` a previous target's job, read its output, branch on the contents.

In regime 3, **graph construction and graph execution are genuinely interleaved**. There is no single graph artifact that exists before execution starts. Graph-level fingerprinting and caching lose meaning; you drop to per-node content-addressed caching.

### 11.4 Regime detection

The checks in §10.11 — `grep` for `target`, `module_facet`, `library_facet`, `extern_lib`, and `precompileModules` across `lakefile.lean` plus every `.lake/packages/*/lakefile.*` — are the regime-3 detector. Mathlib passes: its lakefile uses only static declarations. The only question is whether upstream packages (batteries, Qq, aesop, proofwidgets, …) ever introduce regime-3 constructs; the check must be recursive.

### 11.5 Why this matters for distribution

- Regime 1/2 → full graph up front → trivially distributable across a worker pool.
- Regime 3 → graph can only be completed mid-build → distributed execution adds synchronization points per discovery (Bazel handles this via `dynamic_deps`, but it is a real architectural tax).

For mathlib4 today: maximally cleanly distributable.

---

## 12. Fingerprinting and graph-level caching

Given a build graph, two independent caching layers apply:

### 12.1 Graph-level cache (only meaningful in regimes 1–2)

Purpose: avoid re-running graph construction when nothing that could affect the graph has changed.

Fingerprint composition:

1. Sorted `(path, sha256(content))` for every file the graph constructor read — lakefiles across the whole dependency tree, `lake-manifest.json`, `lean-toolchain`, and the header prefix of every `.lean` file.
2. Sorted `(name, value_or_<unset>)` for every env var the constructor consulted.
3. Sorted content hashes of every file in the graph-construction roots (`Mathlib/`, `MathlibTest/`, etc.), limited to headers — catches added/removed modules and `import` changes.
4. Lake CLI flags affecting graph shape: `-K`, `--buildType`, `--packages`.
5. Hash of the Lake binary itself (captures DSL semantics changes across Lake upgrades).

Match → replay cached graph. Miss → re-run construction.

**Soundness hazards:**

- **Untraced reads.** If construction code reads a file through an uninstrumented path, the fingerprint misses that dependency. Mitigation: instrument the general `IO.FS.*` primitives at the Lake layer, not just suspected call sites.
- **Filesystem enumeration.** A new `.lean` file must invalidate. Include *directory listings* (not just contents) in the fingerprint — every `readDir` at graph-time extends it.
- **Nondeterministic construction.** Canonicalise the emitted graph (sort nodes by id, sort inputs/outputs lexically) before hashing.
- **Path-style `require`s.** Must traverse recursively into the required directory.
- **Time/PID/random.** A tracer at graph-time should refuse these calls (panic) or at minimum record them to ban them.

### 12.2 Node-level cache (works in all regimes)

Purpose: skip individual build actions whose inputs are unchanged. This is the standard content-addressed build cache (Bazel RBE, Nix, mathlib's own `lake exe cache`).

```
node_cache_key = sha256(normalized_command, sorted_env, sorted(input_content_hashes))
node_cache_key → {output_content_hashes}
```

`lake exe cache` demonstrates this works for mathlib4: olean outputs are effectively content-addressable.

### 12.3 How much does graph-level caching actually buy?

For mathlib4 today: very little. Reading `graph_deps` and rehashing headers is the same work as constructing the static graph from scratch (§6) — seconds either way. The graph-level cache pays off only when graph construction is expensive *and* repeated: regime-2 projects that shell out in their lakefiles, or instrumented Lake runs that pay a tracing overhead.

The real caching value for distributed execution is at the **node level** — caching ~10000 `lean` invocations. The graph-level discussion is a footnote next to that.

---

## 13. Distributed execution: what actually matters

Given the goal is running the graph across a worker pool, the requirements reduce to:

1. **Full graph enumerated before dispatch** — scheduler cannot stream-discover nodes efficiently.
2. **Each node is hermetic** — a remote worker produces the outputs without consulting a central brain.
3. **Content-addressed inputs/outputs** — no shared filesystem assumption.
4. **Deterministic outputs** — bit-identical for cache hits.

Mathlib is well-positioned on 1, 3, 4: regime 1 → trivial enumeration; Lake's native artifact cache (`Lake.Artifact`, `Lake.CacheMap`, `lake cache get/put`) provides content-addressability natively as of v4.30; Lean strives for bit-reproducibility.

### 13.1 Lake's native cache provides hermeticity for free

Lake itself is a content-addressed build system. During `lake build`, Lake computes each module's input hash, calls `(← getLakeCache).readOutputs? scope inputHash`, and on hit, hardlinks artifacts from `cache.artifactDir` into `.lake/build`. On miss, builds and calls `saveArtifact` to populate the cache (`Lake/Build/Common.lean:459, 518`). `lake cache get/put/add/stage` (`Lake/CLI/Main.lean:383-650`) provides remote sync against Reservoir or a custom HTTP endpoint. As of `leanprover/lean4#12634` (2026-03-03), `lake cache get` defaults to lazy fetching — downloads mappings only; artifacts are pulled during `lake build` per input-hash lookup.

This means a distributed-build pipeline does not need to design a custom CAS, materialization protocol, or executor:

```
[extract]  lake graph-extract <target> → manifest + sidecars  (shard planning data)

[plan]     orchestrator computes a topo-level partition across N matrix workers

[shard N]  lake cache get [<shard's mappings>]   ← lazy fetch from cache service
           lake build <shard's modules>           ← Lake handles cache hit/miss
           lake cache put                         ← upload new artifacts

           (`needs:` between shard topo levels so downstream sees upstream's `cache put`)
```

Lake's `Hash` is the cache key. The orchestrator's role is partitioning the closure; execution and CAS are Lake's job.

### 13.2 Input fanout and locality

`Mathlib.lean` lists **8310 transitive imports**. A naive distributed scheme has each worker materializing tens of GB on cold cache. Lake's lazy fetch (mappings-first, artifacts on demand) plus hardlink-from-CAS-into-`.lake/build` already addresses most of this — the worker only fetches artifacts whose input hash a build actually requests.

Sharding strategies that further reduce duplication:
- **Topo-level greedy bin-packing** — partition each topo level across workers; barrier between levels. ~80% of optimal, simple to implement.
- **Critical-path-first** — schedule along the longest chain first; needs realistic per-node duration estimates.

### 13.3 What still requires care

- **Sidecar materialization.** Lake's cache-hit logic reads `.olean.hash` and `.trace` sidecars, not just `.olean`. Any system that materializes oleans into `.lake/build` MUST also materialize the corresponding sidecars or Lake will rebuild. Lake's own `saveArtifact` hardlinks all of them; mathlib's legacy `Cache/IO.lean:292-307` packs the same set in `.ltar` archives. Empirically validated 2026-05-04: deleting `.olean.hash` while keeping `.olean` causes Lake to rebuild the module.
- **Coexistence with mathlib's legacy `Cache/`.** The Python `lake exe cache get` infrastructure remains the local-dev cache. CI will use Lake's native cache. `Cache/README.md` confirms eventual replacement; no active migration PR as of 2026-05-04.

### 13.4 Regime-detection is a distribution-cleanliness check

Re-reading §11 through the distribution lens:

- Regime 1 → full graph before dispatch → no runtime coordination → cleanest.
- Regime 2 → full graph after a fast elaboration phase → still clean.
- Regime 3 → partial graph, extended mid-build → scheduler needs to accept node-level extensions at runtime, adding round-trips and stalling dependent work.

So the §10.11 health check is not just a "is static extraction sound?" test — it is a **"can I distribute this without paying a synchronization tax?"** test.

---

## 14. Instrumentation fallback, revisited for the distributed case

If §10.11 ever fails (mathlib enters regime 2 or 3), the recovery path is:

1. **Patch Lake** at `compileLeanModule`, `compileO`, `compileExe`, and custom-target dispatch to emit `{command, env, inputs, outputs, graph_deps, env_deps, exec_deps}` per node as it is constructed. (See §9 for call sites.)
2. **Trace graph-construction IO** to populate `graph_deps`/`env_deps`: wrap `IO.FS.readFile`, `IO.FS.readDir`, `IO.getEnv` during elaboration.
3. **Emit with distribution-ready shape** (relative paths, pre-computed `setup.json` per node, input content hashes). The relativization happens at emission time, before the graph leaves the local machine.
4. **Fingerprint the observed graph-construction inputs** (§12.1). Subsequent runs rehash cheaply and skip re-instrumentation when the fingerprint holds.
5. **In regime 3**, the emitted "graph" is actually a forest of sub-graphs with dependencies on upstream *output contents*. Either model these as runtime-extension points for the scheduler (Bazel `dynamic_deps` equivalent), or flatten by running the dynamism-introducing targets locally before dispatch and treating their outputs as source-level inputs to the rest of the graph.

---

## 15. Implementation status

The extraction tool described above has been implemented as a Lake-side subcommand: `lake graph-extract` in `Lake/Build/GraphExtract.lean`. The original Python prototype that drove this analysis was superseded; the current state is captured in:

- `lake_graph_extract_handoff.md` — implementation status, commits, working-tree layout, next steps.
- `lake_graph_extract.md` — design reference (schema, architecture, validation harness).
- `lake_facets_for_extraction.md` — facet purity rules the walker depends on.
- `lake_upstream_feasibility.md` — strategy for upstreaming to `leanprover/lean4`.
