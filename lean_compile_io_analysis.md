# What a single `lean` invocation reads and writes when Lake builds a mathlib module

Companion to [`lake_build_graph_analysis.md`](./lake_build_graph_analysis.md) and
[`lake_graph_extract.md`](./lake_graph_extract.md). Those documents establish that mathlib's Lake
build graph can be reconstructed statically. This document zooms in one level: for *one* node in
that graph (a `lean_module` node), what files does the `lean` process actually open, and what does
it write? The goal is to answer:

> Can we statically determine, ahead of execution, the complete read/write file set of a single
> mathlib module compilation?

The answer is **yes, with two caveats** documented in §6:
- The toolchain's `Init.olean` tree is read via `LEAN_PATH` fallback rather than `importArts` and
  must be staged on the worker (it isn't enumerated in setup.json).
- Tactic-level `IO` is in principle unrestricted; mathlib doesn't exercise this, but the static
  guarantee is "no IO if no tactic does IO," not unconditional.

The analysis is grounded in the Lean source tree at `/Users/chelo/lean4/src/` and in the Lake
source at `/Users/chelo/lean4/src/lake/`, with Mathlib at `/Users/chelo/mathlib4/`.

---

## 1. Running example: `Mathlib.Algebra.Group.Basic`

Picked because it sits in the middle of the build graph, has a non-trivial dependency fan-in, and
is module-style (representative of post-module-system mathlib).

**Source file:** `Mathlib/Algebra/Group/Basic.lean`. Header (verbatim):

```lean
module

public import Aesop
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs
```

**setup.json** (`.lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json`) summary:
- `name = "Mathlib.Algebra.Group.Basic"`, `package = "mathlib"`
- `isModule = true`
- `plugins = []`, `dynlibs = []`
- `options = mathlibLeanOptions` (9 keys, mostly weak linter flags)
- `importArts = { 266 entries }` — every entry is size 3 (`[olean, ir, olean.server]`); none is
  size 4 (no `import all` reaches this module)

**Direct inputs declared by the Lake graph extractor for this node:**

```
src:        Mathlib/Algebra/Group/Basic.lean
setup_json: .lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json
import_art: 3 paths × 266 modules = 798 olean/ir/olean.server files
```

**Outputs the `lean` invocation produces:**

```
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean         (583K)
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean.server   (96K)
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean.private  (1.2M)
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.ir              (9K)
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.ilean          (104K)
.lake/build/ir/Mathlib/Algebra/Group/Basic.c                    (12K)
```

(`.hash` sidecars are written by Lake separately, not by `lean`. So is the `setup.json` itself —
Lake writes it before invoking `lean` per `Lake/Build/Actions.lean:86`.)

**Command (paths abbreviated, captured from `lake build -v --no-cache`):**

```
LEAN_PATH=<colon-separated package lib dirs> \
  $TOOLCHAIN/bin/lean \
  $WORKSPACE/Mathlib/Algebra/Group/Basic.lean \
  -o .lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean \
  -i .lake/build/lib/lean/Mathlib/Algebra/Group/Basic.ilean \
  -c .lake/build/ir/Mathlib/Algebra/Group/Basic.c \
  --setup .lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json \
  --json
```

This is the canonical mathlib `lean_module` node shape.

---

## 2. The `lean` binary's IO surface during compilation

Trace from `Lean/Shell.lean:521` (the `--setup` handler) downstream:

```
ModuleSetup.load setupFileName?            -- reads JSON
runFrontend  ← Lean/Elab/Frontend.lean
  setup.dynlibs.forM Lean.loadDynlib       -- dlopen each dynlib
  Language.Lean.process { setup }
    setupImports stx                       -- merges header + setup
    processHeaderCore .. arts:=importArts
      importModules .. plugins arts
        plugins.forM Lean.loadPlugin       -- dlopen + initialize each plugin
        importModulesCore imports arts
          loop over transitive imports:
            loadData i = if i ∈ arts: read arts.oleanParts(...)
                         else:        findOLean ⇒ readModuleDataParts
            loadIR?  i = if i ∈ arts: read arts.ir? (if any)
                         else:        read findOLean(i).withExtension "ir"
        finalizePersistentExtensions       -- runs init code, may load more
        runInitAttrs                       -- runs `[init]` from imported oleans
  process commands ...                     -- elaboration; tactics may do IO
  writeModule env oleanFile (writeIR := !postponeCompile)
    saveModuleDataParts mainModule [exported, server, private]
    saveModuleData (fname.withExtension "ir") (...) (mkIRData env)
  writeFile ileanFile (toJson ilean)
  if trace.profiler.output: writeFile profile.json    -- not enabled in mathlib
emitC mainModuleName ⇒ write to cFile     -- when -c given
emitLLVM env mainModuleName bcFile        -- when -b given (mathlib doesn't)
```

This is the *complete* IO surface of `lean` for a Lake-driven module compile, modulo what
elaboration itself triggers (covered in §5).

---

## 3. Inputs read

Precise per-call breakdown for our running example.

### 3.1 The source file

```
read: $WORKSPACE/Mathlib/Algebra/Group/Basic.lean
```

Read once via `Parser.mkInputContext input fileName` after `IO.FS.readFile` at the shell layer.
Static input.

### 3.2 The setup.json

```
read: $WORKSPACE/.lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json
```

`Lean/Setup.lean:163` (`ModuleSetup.load`) reads and parses it. After this point Lean has the full
`ModuleSetup` in memory; the file is not reopened.

### 3.3 Olean parts of imported modules

The decision tree, from `Lean/Environment.lean:2129-2143`:

```lean
loadData i := do
  let fnames ← if let some arts := arts.find? i.module then
    pure (arts.oleanParts (inServer := globalLevel ≥ .server))
  else
    findOLeanParts i.module
  readModuleDataParts fnames
```

Two paths.

**Path A (`importArts` hit).** Each entry in `importArts` is an `ImportArtifacts` — an array of
file paths — whose *length* encodes the import's category. Three sizes are emitted, corresponding
to three categories of import (full chain in §5.1; summary here):

| Entry size | Category | Where Lake decides | Files in the array |
|---|---|---|---|
| 1 | The imported module is **not module-style** (legacy header, no `module` keyword) | `Lake/Build/Module.lean:466,469` — built when the imported module's `input.header.isModule = false` | `[olean]` |
| 3 | The imported module **is module-style**, and the importer used a plain `import` (not `import all`) | `Lake/Build/Module.lean:452` — built when `input.header.isModule = true`, picked when `importAll = false` at line 242 | `[olean, ir, olean.server]` |
| 4 | The imported module is module-style, and the importer used `import all` | `Lake/Build/Module.lean:455` — same builder as size 3 but picked when `importAll = true` at line 242 | `[olean, ir, olean.server, olean.private]` |

So "size" is jointly determined by *the imported module* (whether it is itself module-style) and
*how this importer reaches it* (plain `import` vs. `import all`, propagated through the lattice).
The whole import graph is walked in `fetchTransImportArts` (`Lake/Build/Module.lean:222-255`): it
threads an `importAll` flag down the DFS, picks `info.allArts` when the flag is set and `info.arts`
otherwise (line 242), and may *promote* an existing size-3 entry to size 4 on revisit if a later
path reaches the same module via `import all` (lines 236-240).

`oleanParts` (`Lean/Setup.lean:92-103`) is the consumer-side selector — given an entry and the
current `inServer` flag, it picks which of those paths `lean` will actually open:

| Entry size | What `lean` actually opens (non-server build, the `lake build` case) |
|---|---|
| 1 | `[olean]` |
| 3 | `[olean]` only — `.olean.server` is *listed* but **not** opened unless `inServer || privateExists` |
| 4 | `[olean, olean.server, olean.private]` |

The asymmetry — Lake always lists `.olean.server` for module-style imports but `lean` opens it
only conditionally — is intentional; the comment in `Setup.lean:97-100` notes "For uniformity,
Lake always provides us with .olean.server, so load it only when we are in server mode or we need
it to load further files."

For our example: `Mathlib.Algebra.Group.Basic` has 266 importArts entries, **all size 3** (every
imported module is module-style; the source file uses plain `public import`, never `import all`),
`globalLevel = .exported`, not in server. So each of the 266 imports contributes exactly **one
olean read** — `.olean.server` files are listed in setup.json but never opened by this `lean`
process.

The `.ir` element of size-3+ entries is consumed by a separate function — see §3.4.

**Path B (`findOLean` fallback).** Walks `LEAN_PATH` for `<module>.olean` (and opportunistically
`.olean.server`/`.olean.private` if they exist).

This fallback fires for any module **not** keyed in `importArts`. In a fully Lake-driven mathlib
build the only such module is **`Init`** (verified empirically — `Init` is *not* a key in
`Mathlib.Algebra.Group.Basic.setup.json`). It is loaded from the toolchain's
`<TOOLCHAIN_ROOT>/lib/lean/Init.olean` via the search path's built-in entry (`getBuiltinSearchPath`
in `Lean/Util/Path.lean:107-109`).

`Init` is reached because `HeaderSyntax.imports` (`Lean/Elab/Import.lean:27-37`) implicitly prepends
`{ module := `Init }` whenever the source file lacks the `prelude` keyword. `Mathlib.Algebra.Group.Basic`
has `module` but no `prelude`, so `Init` is injected.

The `Init` closure is non-trivial (Lean core's prelude tree). Once loaded, `goRec` walks `Init`'s
own imports — those are also resolved via `findOLean`, since they too aren't in `importArts`. So
the toolchain's entire `lib/lean/Init/**` subtree is reachable.

### 3.4 IR files of imported modules

Separate loader, same control flow:

```lean
loadIR? i := do
  let irFile? ← if let some arts := arts.find? i.module then
    pure arts.ir?
  else
    let irFile := (← findOLean i.module).withExtension "ir"
    pure (guard (← irFile.pathExists) *> irFile)
  irFile?.mapM (readModuleData ·)
```

The `.ir` file is read **per-import**, only when the lattice in `importModulesCore` flags
`needsIR` (`Lean/Environment.lean:2089`). `needsIR := needsIRTrans || importAll || globalLevel > .exported`.
For module-style compilation with `globalLevel = .exported` and no `import all`/`meta` annotations,
many imports skip IR loading. For our example, IR is loaded only for imports reached transitively
through a `meta import` chain.

So `.ir` files in setup.json are **conservatively declared inputs** that aren't always opened.
That's fine for hermeticity; for cache-key minimization there is overcounting, but Lean itself
doesn't expose the actual minimum read set without running through `importModulesCore`.

### 3.5 Plugins

```lean
plugins.forM Lean.loadPlugin
```

`loadPlugin` (`Lean/LoadDynlib.lean:93`):

1. `IO.FS.realPath path` — resolves symlinks, reads `path` metadata.
2. `Dynlib.load path` — `dlopen` (or `LoadLibrary` on Windows).
3. `dynlib.get? "initialize_<modulename>"` — symbol lookup.
4. `sym.runAsInit` — runs the module initializer in the loaded library.

`dlopen` itself reads:
- the plugin `.so`/`.dylib`/`.dll`
- every `DT_NEEDED` (or `LC_LOAD_DYLIB`) library it transitively links against — `libleanshared`,
  `libc`, `libm`, package-bundled shared libs, etc.

For `Mathlib.Algebra.Group.Basic`, `plugins = []`, so this is a no-op. The §10.5 preflight in the
extractor enforces this for every mathlib module.

### 3.6 Dynlibs

Same loader as plugins minus the initializer step (`Lean.loadDynlib`, `LoadDynlib.lean:67`).
`dlopen`'d at the start of `runFrontend` so that `@[extern]` declarations elaborated later in the
file can resolve their symbols against the loaded library.

For mathlib: `dynlibs = []` everywhere (enforced by preflight).

### 3.7 The `lean` binary itself and its linked libraries

The `lean` ELF/Mach-O binary plus `libleanshared.{so,dylib}`, `libInit_shared`, `libc`, etc., are
opened by the OS loader before `main` runs. Not visible at the Lean level but they are real
*inputs* for hermeticity: the worker must stage the toolchain.

### 3.8 No other implicit reads

Beyond §3.1–§3.7, `lean --setup --json -o .. -i .. -c ..` does **not** read any other configuration
file. Specifically:

- No `lean.toml` / project config — Lake's responsibility, lifted into setup.json.
- No `~/.lean` user config.
- No `LEAN_SRC_PATH` lookup during compilation (only `printImportSrcs`, an unused subcommand).
- No environment variables read during compilation. `IO.getEnv` is used by initialization
  (`addSearchPathFromEnv` at startup pulls in `LEAN_PATH`) but not by any per-import logic.

`getBuiltinSearchPath` at startup (`Lean/Util/Path.lean:108`) reads `LEAN_PATH` once and combines
with the toolchain's `lib/lean/`. This determines `findOLean` behavior for §3.3 path B but is not
itself a file read.

### 3.9 Total read set for the running example

```
1   .lean source file
1   setup.json
266 .olean files                 (path A, importArts)
≤266 .olean.server               (only when private exists or in server mode → 0 here)
0   .olean.private               (no size-4 entries)
?   .ir files                    (subset depending on `meta import` reachability; declared 266)
1+  Init.olean + Init.ir + Init.* transitive closure  (path B, via LEAN_PATH)
0   plugins / dynlibs
N   toolchain shared libraries   (dlopen by OS loader at startup)
```

For our example: ~266 declared `importArts` files actually opened plus ~50 toolchain `Init.*`
files. Static enumeration is exhaustive *given* a static toolchain blob.

---

## 4. Outputs written

Three driven by CLI flags (the Lake template always passes `-o`, `-i`, `-c`):

### 4.1 The olean parts (`-o`)

`writeModule` (`Lean/Environment.lean:1829-1841`):

```lean
def writeModule (env : Environment) (fname : System.FilePath) (writeIR := true) : IO Unit := do
  if env.header.isModule then
    saveModuleDataParts env.mainModule #[
      (← mkPart .exported),                       -- fname.olean
      (← mkPart .server),                         -- fname.olean.server
      (← mkPart .private)]                        -- fname.olean.private
    if writeIR then
      saveModuleData (fname.withExtension "ir") ... (mkIRData env)
  else
    saveModuleData fname env.mainModule (← mkModuleData env)
```

For module-style files (mathlib's standard): writes 3 olean parts plus a separate `.ir` file in
the same directory. `writeIR` is gated on `!Compiler.compiler.postponeCompile`; mathlib's lakefile
doesn't postpone, so `.ir` is always emitted.

For non-module files (legacy Lean 4 style): writes a single `.olean`.

### 4.2 The ilean (`-i`)

`Frontend.lean:200-211`. Collects info trees from the snapshot graph, runs
`Lean.Server.findModuleRefs` over them, serializes the result to JSON, writes to disk. Pure
function of the elaborated file; no external reads beyond what elaboration already did.

### 4.3 The C output (`-c`)

`Shell.lean:539-546`. Opens a fresh handle for write, runs `Compiler.LCNF.emitC mainModuleName`
against the final environment, dumps UTF-8 bytes. Pure function of `env`.

### 4.4 The bytecode output (`-b`)

`Shell.lean:547-550`. Mathlib doesn't pass `-b`; LLVM backend is unused. Worth knowing it exists so
that "Lake adds `-b` for some lib" trips the validators rather than silently appearing.

### 4.5 Optional profiler output

`Frontend.lean:213-216`. Only fires if `trace.profiler.output` is set in `Options`. Mathlib doesn't
set this. Listed for completeness.

### 4.6 No other writes

Specifically, `lean` does **not** write:
- `.hash` files (Lake writes those after the `lean` process exits, against the produced artifacts)
- `.trace` files (same)
- The `setup.json` itself (Lake wrote it before invocation)

So Lake's per-module artifact directory ends up populated by *both* Lake and `lean`, with Lake
owning the metadata sidecars and `lean` owning the compilation outputs.

### 4.7 Total write set for the running example

```
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean.server
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.olean.private
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.ir
.lake/build/lib/lean/Mathlib/Algebra/Group/Basic.ilean
.lake/build/ir/Mathlib/Algebra/Group/Basic.c
```

Six files, all listed by the extractor's `outputs` field. Static.

---

## 5. The module system's effect on what gets read

The module system (`module` / `public import` / `import all` / `meta import`) reshapes the per-file
load set in three ways. All three are decidable from the parsed import graph + setup.json without
running anything.

### 5.1 `oleanParts`: which of the (olean, server, private) triple actually opens

From `Lean/Setup.lean:92-103`, the file-selection function for one import:

```lean
def ImportArtifacts.oleanParts (inServer : Bool) (arts : ImportArtifacts) : Array System.FilePath :=
  Id.run do
    let mut fnames := #[]
    if let some mFile := arts.olean? then
      fnames := fnames.push mFile
      if let some sFile := arts.oleanServer? then
        if inServer || arts.oleanPrivate?.isSome then
          fnames := fnames.push sFile
        if let some pFile := arts.oleanPrivate? then
          fnames := fnames.push pFile
    return fnames
```

"Module-style" means the source file's header begins with the `module` keyword (Lean 4's module
system, contrasted with the legacy header that omits it). `HeaderSyntax.isModule`
(`Lean/Elab/Import.lean:24`) is just `!header.raw[0].isNone` — i.e., is the first header token
the `module` keyword? That single bit propagates through three places, and the chain is what
ultimately decides which files `lean` opens for each import.

**Step 1: Lake builds the imported module.** When Lake compiles module `B`, it inspects `B`'s
*own* header (via `Module.recFetchInput` at `Lake/Build/Module.lean:30-38`, which calls
`Lean.parseImports'`). The parsed header carries `isModule : Bool`. This bit decides what file set
exists on disk after `B` is built:

- If `B.isModule = false` (legacy): only `B.olean`, `B.ilean`, `B.c` exist.
- If `B.isModule = true` (module-style): also `B.olean.server`, `B.olean.private`, `B.ir` exist.

Source: `Lake/Build/ModuleArtifacts.lean:16-26` and the `mkArtifacts` call at
`Lake/Build/Module.lean:857`.

**Step 2: Lake constructs `B`'s `ImportArtifacts` summary.** When some other module `A` is going
to import `B`, Lake needs to tell `lean` (via `A`'s setup.json) which of `B`'s files to open.
Lake builds *two* candidates per imported module, in `Module.lean:442-474`:

```lean
if input.header.isModule then                          -- B is module-style
  return {
    arts    := .ofArray #[olean, ir, oleanServer]                  -- size 3
    allArts := .ofArray #[olean, ir, oleanServer, oleanPrivate]    -- size 4
    ...
  }
else                                                   -- B is legacy
  return {
    arts    := ⟨#[olean]⟩                              -- size 1
    allArts := ⟨#[olean]⟩                              -- size 1 (same)
    ...
  }
```

So `arts` and `allArts` are pre-computed for every imported module: a "default" path list and an
"if the importer asked for `import all`" path list. The shape of the legacy case (size 1, identical
in both fields) reflects that legacy modules have no `private`/`server` content to expose.

**Step 3: Lake walks `A`'s transitive imports and picks one of the two per entry.** This happens
in `fetchTransImportArts` (`Module.lean:222-255`). The walker DFS-traverses the graph, threading an
`importAll : Bool` flag, and for each module `B` encountered:

```lean
let arts := if importAll then info.allArts else info.arts
```

(`Module.lean:242`). Where does `importAll` come from for that visit?

- It starts as `imp.importAll` for each direct import — the `import all Foo` syntax sets the bit.
- It is propagated transitively: line 253 enqueues `B`'s own imports with
  `importAll && imp.importAll`, i.e., `import all` is sticky only along chains where every step
  also says `import all`. (Plus a `nonModule` short-circuit for legacy importers, irrelevant for
  mathlib.)
- Lines 236-240 implement the "promote on revisit" rule: if `B` was already inserted with
  `arts.size == 3` and a later path arrives with `importAll = true`, Lake re-fetches and replaces
  with the size-4 entry. This makes the per-module choice the lattice join across all paths.

So the *size* of each entry in `A`'s setup.json is the answer to two questions:

1. **Is the imported module module-style?** (Answered by `B.header.isModule`.)
   - No → size 1 (legacy).
   - Yes → either size 3 or size 4.
2. **Does any path from `A` reach `B` through a chain of `import all`?**
   - No → size 3.
   - Yes → size 4.

The result is the encoding `lean` will see:

| Size | Meaning | Files in the array |
|---|---|---|
| 1 | imported `B` is legacy (non-module-style) | `[olean]` |
| 3 | imported `B` is module-style; importer reaches it without `import all` | `[olean, ir, olean.server]` |
| 4 | imported `B` is module-style; importer reaches it via `import all` | `[olean, ir, olean.server, olean.private]` |

**Step 4: `lean` consumes the encoding.** `oleanParts` (the function shown above) maps the size
to a *read set*, parameterised by `inServer`. Combined with the lattice in `importModulesCore`,
this gives the per-import file-open count:

- Size 1: 1 read (`.olean`).
- Size 3, normal `lake build`: 1 read (`.olean`). The `.olean.server` path is *in the array* but
  Lean's selector only pushes it onto the read list when `inServer || privateExists`; here
  neither holds, so the file stays unopened.
- Size 3, `lake setup-file` (LSP): 2 reads (`.olean`, `.olean.server`) — the LSP needs server-only
  metadata for hover/goto-def.
- Size 4: 3 reads (`.olean`, `.olean.server`, `.olean.private`) — `import all` exposes the
  importee's private declarations to the importer.

(The `.ir` element, slot 1, is consumed separately by `loadIR?`; see §3.4 for when it actually
opens.)

**Why the asymmetry between the on-disk array and the open list?** The comment at
`Lean/Setup.lean:97-100` says it directly: "For uniformity, Lake always provides us with
.olean.server, so load it only when we are in server mode or we need it to load further files."
Lake encodes the union of what *might* be needed; `lean` decides what *is* needed at this
invocation. The static read set the extractor declares is the union (sound, slightly
over-declared); the actual read set is a function of the size encoding plus `inServer`.

**Tying it back to the running example.** `Mathlib.Algebra.Group.Basic`:

- The header begins with `module` → the *file being compiled* is module-style. Its `globalLevel`
  is `.exported` (not `.server` because we're in `lake build`, not the LSP path).
- All 266 entries in its `importArts` are size 3. Reasons: every imported module is itself
  module-style (post-module-system mathlib uniformly is), and the source uses plain
  `public import` for all six direct imports — never `import all`. The transitive walk propagates
  `importAll = false` everywhere, so no entry gets promoted to size 4.
- Per the read-set table above: 266 size-3 entries × 1 file each = 266 olean opens via path A.

This is the chain that justifies the "266 olean reads" figure in §3.9. Change any link — flip an
import to `import all`, downgrade a dependency to legacy non-`module` form, or run inside the LSP
— and the read set shifts in a way that's still computable from the same static data.

### 5.2 `import all` propagation

`importAll` (a flag on the `Import` syntax: `import all Foo`) does two things:

1. Bumps the entry-size selection to 4 → opens `.olean.private` of `Foo`.
2. Recursively bumps the `importAll` flag on `Foo`'s own imports, but only those re-entered via
   the lattice in `importModulesCore` (`Environment.lean:2102-2118`). The lattice keeps a fixed
   point of `(importAll, isExported, irPhases)` per module.

The fixed-point computation is finite and pure. The extractor doesn't need to run it; Lake already
did, and the result is encoded in the size of each `importArts` entry.

### 5.3 `meta import` and IR loading

`isMeta` on `Import` flags an import as needed at compile-time (during elaboration of macros that
reference IR-resident bindings). The propagation rule (`Environment.lean:2088`):

```lean
let needsIRTrans := needsIRTrans || needsData && i.isMeta
let needsIR := needsIRTrans || importAll || globalLevel > .exported
```

`needsIR = true` triggers `loadIR? i` (§3.4). Mid-mathlib modules trigger this for the closure
reached through their `meta import` chains, typically: tactic library imports.

The set of modules with `needsIR = true` is again a fixed point on a static graph, decidable
ahead of time. The extractor can compute it; alternatively, declaring all `.ir` paths as inputs
(the conservative choice it makes today) is sound but over-declared.

### 5.4 `public` / private imports

`public import` exposes the imported module to *this* module's importers; non-`public` imports are
visible only inside this module. This affects *what gets re-exported through the olean*, not what
this compilation reads. Both kinds of import open the same files.

Practically: if `B` is a `public import` in `A`, then a downstream `C` that `import`s `A` will
see `B`'s public declarations transitively, and Lake's transitive-import walker will list `B` in
`C`'s `importArts`. So `public` shifts work *between* modules but doesn't change a single module's
own input set.

### 5.5 `prelude` and the implicit `Init`

Already covered in §3.3 path B. The `module` keyword does **not** suppress `Init`; only `prelude`
does. `prelude` files (Lean core itself) get no `Init` injection. Mathlib has none.

### 5.6 Net: is the read set a function of static data?

Yes. For each transitive import, the file-set is fully determined by:

- The `importArts` size encoded in setup.json (1/3/4) — set by Lake from the import graph.
- The `globalLevel` of the compilation — determined by the source's `module`/non-`module` keyword.
- The `inServer` flag — `false` for `lake build` (true only for `lake setup-file` driven LSP).
- The lattice fixed point on `(importAll, isMeta, isExported)` — pure function of the graph.

No runtime decision changes the file set. The reader can compute the *exact* read set
ahead of time; the extractor's current "list everything in importArts plus setup.json plus source"
strategy is a sound over-approximation.

---

## 6. Tactic IO and other elaboration-time side effects

The previous sections cover the IO that Lean's *infrastructure* performs. Elaboration of the
source file can also do IO, channeled through user code that runs in `MetaM`/`TacticM`/`CommandM`,
all of which are wrappers around `IO`. This is the only category of file access that is *not*
statically determinable from the build graph alone.

### 6.1 What IO is reachable from a tactic?

`Lean.Elab.Tactic.TacticM` is `ReaderT Context (StateRefT State TermElabM)`, and `TermElabM`
ultimately wraps `IO`. So any tactic body can:

- `IO.FS.readFile` / `readBinFile` / `realPath` / `readDir`
- `IO.getEnv` / `IO.appDir` / `IO.currentDir`
- `IO.Process.spawn` / `output` / `run`
- `Dynlib.load` (via `loadDynlib`)
- network IO (less commonly used in Lean tactics; the primitives exist via `Socket`)

A `macro_rules`/`elab_rules` body, an `initialize` block, or an `attribute` callback can reach
the same primitives.

### 6.2 What does mathlib actually do?

The user's stated assumption: mathlib tactics do not perform IO during elaboration. That is the
practical truth — the established elaboration-time tactics (`simp`, `omega`, `polyrith`, `ring`,
`norm_num`, etc.) are pure metaprograms over `Expr`/`Environment`. The few tactics that *do*
shell out (`polyrith`'s SageCell call, some external solvers) are explicitly off by default and
are guarded.

This is a *property of mathlib's elaboration*, not a guarantee from the type system. The Lake
graph cannot enforce it. The build will be correct under the assumption; the worker pool
hermeticity story is correct under the assumption; no static check at the graph layer can falsify
it short of sandboxing the `lean` process itself (e.g., `seccomp`, macOS sandbox profile).

### 6.3 Initializer execution at import time

Even with no tactic IO, `runInitAttrs` (`Environment.lean:1892`, called from
`finalizePersistentExtensions`) runs `[init]` attributes from imported oleans. If a downstream
package's `initialize` block does IO, that IO fires when *any* module that transitively imports
the offending package is compiled.

For mathlib: spot-checked. The `initialize` blocks across mathlib + upstream packages are pure
state-extension registrations. None reach `IO.FS.*` or `IO.Process.*`. But again, this is
empirical, not enforced.

### 6.4 Plugin initializers

`loadPlugin` runs `initialize_<modulename>` from a shared library. Mathlib has no plugins
(`plugins = []` everywhere). If a future package adds one, that initializer is arbitrary native
code with full process privileges. Treat plugins as toolchain-level trust boundaries.

### 6.5 Snapshot-graph profiler output

`trace.profiler.output` writes a Firefox profile JSON. Off by default; mathlib doesn't enable it.
Listed here only because it is the one Lean-internal write that's gated on an option rather than
a CLI flag.

### 6.6 Static-determinability under the no-IO assumption

If we assume "no tactic-level IO and no initializer-level IO":

- The read set is exactly §3.9.
- The write set is exactly §4.7.
- Both are functions of (lakefile + import graph + toolchain version).

Without that assumption, the read set is unbounded in principle. There is no way to make it
static at the graph extraction layer. The honest options are:

1. **Trust mathlib + upstream packages.** Document the assumption; make it part of the workspace's
   accepted invariants alongside the §10.11 preflight.
2. **Sandbox the worker.** Run each `lean` invocation under an OS-level sandbox that filters file
   access against the declared `inputs` whitelist. Failures abort the build with a hermeticity
   error pointing to the offending tactic. This converts "trust" to "verify on every build."
3. **Per-node tracing.** First time each `lean` node runs, capture its read set via `dtruss`/
   `strace`/`fs_usage` and diff against declared inputs. Cache the result and only re-run tracing
   when the source or any input hash changes. This is the Bazel "sandboxed exec + extra inputs"
   pattern.

For a regime-1 mathlib build, option (1) is fine and matches what `lake exe cache` already
implicitly assumes (the cache is content-addressed by inputs, so any hidden read that affects
output content would corrupt the cache and be noticed empirically).

---

## 7. Putting it together: can we statically determine all inputs?

For a single mathlib `lean` invocation, **yes — under three explicit assumptions**:

1. **Regime 1.** The lakefile and every transitive package's lakefile do not contain
   `target`/`module_facet`/`library_facet`/`extern_lib`/`precompileModules`. `lake_build_graph_analysis.md`
   §10.11 enforces this; preflight refuses to emit a graph otherwise.
2. **Toolchain blob staged.** The Lean toolchain (`<TOOLCHAIN_ROOT>/bin/lean`,
   `<TOOLCHAIN_ROOT>/lib/lean/Init.olean` and its full closure, plus `libleanshared`) is treated
   as a separate hashed input set, attached to every node. This covers the §3.3 path B reads.
3. **No tactic-level IO.** Mathlib + upstream packages do not perform `IO` from tactics,
   `initialize` blocks, or plugin initializers. This is empirically true today and not enforced
   by the type system or by Lake.

Under those three assumptions, the per-node read/write set is:

```
read  = { src .lean }
      ∪ { setup.json }
      ∪ ⋃ {olean parts(arts.size)} for each m in importArts
      ∪ ⋃ {.ir} for each m in importArts where needsIR(m)  (over-declared as all .ir is sound)
      ∪ TOOLCHAIN_BLOB                                     (Init.* closure + lean binary)

write = { .olean, .olean.server, .olean.private, .ir, .ilean, .c }   (module-style)
```

All quantities on the right are computable from the lakefile, the parsed import graph (header
parsing only — `lean --deps-json`), and Lake's encoding rules for `importArts` size. None require
running build steps.

### 7.1 Where the existing extractor stands

Cross-check against `lake_graph_extract.md` §4.4:

| Required component | Extractor today |
|---|---|
| `.lean` source | declared (`kind:"source"`) |
| `setup.json` | declared (`kind:"setup_json"`) |
| All olean parts per importArts entry, sized 1/3/4 | declared (`kind:"import_art"`) — sound |
| `.ir` files per importArts entry | declared — sound, over-declared |
| Plugins | not declared (forced empty by preflight) |
| Dynlibs | not declared (forced empty by preflight) |
| Toolchain blob (Init closure + lean + libs) | implicit via `$TOOLCHAIN`/`$TOOLCHAIN_ROOT` placeholders |
| Six output files | declared in `outputs` |

The extractor is sound today for mathlib. Closing the gap to "complete and machine-checkable" needs:

- **Toolchain content hash** folded into `cache_key` (otherwise a toolchain bump silently
  invalidates nothing).
- **Init closure as an explicit input set** — once, hashed once, attached to every node.
  Eliminates the §3.3 path B implicit dependency.
- **Plugin/dynlib production nodes** the day a package introduces them. Today preflight aborts;
  the long-term answer is to model them as `cc_link --shared` nodes with the resulting `.so`
  declared on every consuming `lean_module` node's `inputs`.
- **Optional sandbox/tracer** as a runtime cross-check on the no-tactic-IO assumption (§6.6).

Without those, the extractor is *empirically correct* (verified by the §6 of
`lake_graph_extract.md` validation results: 9/9 `lean_module`, 7/8 `lean_exe` byte-exact). With
them, the extractor is *provably exhaustive* against the IO surface documented above.

---

## 8. References

| Topic | File |
|---|---|
| `--setup` flag handler | `Lean/Shell.lean:419-521` |
| `ModuleSetup` schema and loader | `Lean/Setup.lean:136-167` |
| `runFrontend`: setup → header → import wiring | `Lean/Elab/Frontend.lean:136-220` |
| `processHeaderCore` → `importModules` | `Lean/Elab/Import.lean:45-69` |
| `importModulesCore` and the `loadData`/`loadIR?` decision tree | `Lean/Environment.lean:2013-2143` |
| `oleanParts` (file-selection from arts) | `Lean/Setup.lean:92-103` |
| `findOLean` / `LEAN_PATH` fallback | `Lean/Util/Path.lean:107-124` |
| `writeModule` (olean+ir output) | `Lean/Environment.lean:1829-1841` |
| ilean serialisation | `Lean/Elab/Frontend.lean:200-211` |
| C emission | `Lean/Shell.lean:539-546` |
| Plugin / dynlib loading | `Lean/LoadDynlib.lean:33-115` |
| Lake's setup-file writer (where setup.json comes from) | `Lake/Build/Actions.lean:86` |
| Lake's importArts encoding (sizes 1/3/4) | `Lake/Build/Module.lean:222-255` |
| Implicit `Init` injection | `Lean/Elab/Import.lean:27-37` |
