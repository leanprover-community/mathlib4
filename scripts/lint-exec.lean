/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

/-!
# `lake exe lint-exec`: flag elaboration-time code execution

This linter flags constructs that execute arbitrary code when a file is elaborated, or that let
the runtime behaviour of a definition diverge from its logical definition:

* `#eval`, `#eval!`, `run_cmd`, `run_meta`, `run_elab`, `run_tac`: run code while the file is
  elaborated;
* `initialize`, `builtin_initialize`, `@[init]`: run code every time the module is imported;
* `unsafe`, `@[implemented_by]`, `@[extern]`: bypass the type checker for compiled code.

Any of these outside the uses listed in `scripts/nolints-exec.txt` is an error.
Elaborating a file runs all of these on CI, on the machine of every reviewer who opens the file in
an editor, and (for `initialize`) in every downstream project, so new uses need review.

## How it works

The linter *parses* files; it does not elaborate them. Each file is processed in its own process
(as `lean` itself does): its header is parsed, the modules it imports are loaded from the compiled
`.olean` files (so that the file is parsed with exactly the syntax it can see), every command is
parsed and its syntax tree is walked for the node kinds above, including inside quotations,
attributes and `… in` wrappers. Nothing from the file is executed: no proof is checked, no tactic
runs, no `#eval` runs, no initializer runs.

The one exception is that commands which change the *parser* for later commands in the same file
(`namespace`, `open`, `notation`, `syntax`, `macro`, …) are elaborated, because otherwise ordinary
files with local notation would not parse. `macro` and `elab` (also inside `… in`, `scoped[NS]`
and similar wrappers) only have their `syntax` half installed; their bodies are never even
defined. After the first disallowed finding in a file the linter stops elaborating `syntax`,
`macro` and `elab` (the commands that could refer to a parser defined in the file) and only parses.

Loading an `.olean` with extensions runs that module's initializers, so the `.olean`s must be
trusted: in Mathlib's CI they come from the cache, which only ever holds builds of files that are
on `master` or that previously passed this linter. Locally, run the linter before `lake build`
if that matters to you. Imports whose `.olean` is missing (files new in a PR, or a project that
has not been built yet) are handled by replaying their parser-affecting commands from source.

A file that does not parse is reported as a finding (`parse-error`), and so is an import that
can be neither loaded nor found (`missing-import`): a file the linter cannot vouch for fails.

## Usage

```
lake exe lint-exec [--allowlist FILE | --no-allowlist] [--root DIR] [--github]
  [--emit-allowlist] [--files-from FILE] [--jobs N] [--verbose] FILE...
```

* `--allowlist FILE`: the allowlist to use (default `scripts/nolints-exec.txt`, relative to the
  root; a missing file means an empty allowlist). Each line is `path: construct=N …`, allowing
  `N` uses of `construct` in that file (`construct` alone means one); lines starting with `#`
  are comments.
* `--no-allowlist`: allow nothing.
* `--root DIR`: directory that file paths and allowlist entries are relative to (default `.`).
* `--github`: print findings as GitHub Actions error annotations.
* `--emit-allowlist`: instead of reporting, print the allowlist that would silence all findings.
  Only use this on a tree you trust: it keeps setting up notation after findings.
* `--files-from FILE`: read additional file paths, one per line, from `FILE`.
* `--jobs N`: number of files to process in parallel (default: number of processors).
* `--verbose`: report commands whose elaboration failed while setting up notation.

Run from the project via `lake exe` (or `lake env`) so that the `.olean` files are found. In a
downstream project, `lake exe mathlib/lint-exec` selects Mathlib's executable unambiguously.
-/

open Lean Elab Command Parser System

namespace LintExec

/-- Syntax kinds that are flagged, with the construct name used in messages and allowlists. -/
def flaggedKinds : List (Name × String) := [
  (``Lean.Parser.Command.eval, "#eval"), (``Lean.Parser.Command.evalBang, "#eval"),
  (`Lean.runCmd, "run_cmd"), (`Lean.runMeta, "run_meta"), (`Lean.runElab, "run_elab"),
  (``Lean.Parser.Tactic.runTac, "run_tac"),
  (``Lean.Parser.Command.initialize, "initialize"),
  (``Lean.Parser.Command.unsafe, "unsafe"), (``Lean.Parser.Term.unsafe, "unsafe"),
  (``Lean.Parser.Attr.extern, "@[extern]")]

/-- Attributes without a dedicated syntax kind: they parse as `Lean.Parser.Attr.simple` and are
recognised by name. -/
def flaggedAttrs : List (Name × String) := [
  (`implemented_by, "@[implemented_by]"), (`init, "@[init]"), (`builtin_init, "@[init]")]

/-- Construct name for parse errors in the allowlist. -/
def parseErrorConstruct : String := "parse-error"

/-- Construct name for imports that can be neither loaded nor replayed. -/
def missingImportConstruct : String := "missing-import"

/-- Commands that are elaborated because they affect how later commands parse. Everything else is
only parsed. -/
def scopingKinds : List Name := [
  ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
  ``Lean.Parser.Command.open, ``Lean.Parser.Command.set_option, ``Lean.Parser.Command.universe,
  ``Lean.Parser.Command.syntaxCat, ``Lean.Parser.Command.syntax,
  ``Lean.Parser.Command.syntaxAbbrev, ``Lean.Parser.Command.notation,
  ``Lean.Parser.Command.mixfix, ``Lean.Parser.Command.binderPredicate,
  ``Lean.Parser.Command.macro, ``Lean.Parser.Command.elab,
  `Mathlib.Notation3.notation3]

/-- The subset of `scopingKinds` that can refer to a parser *defined in the file* (`syntax`
takes arbitrary parser names, and `macro`/`elab` declare `syntax`). After a disallowed finding
these are no longer elaborated, so that a flagged `unsafe def myParser` can never be run; the
others (whose syntax is built from atoms, precedences and categories only) still are, so that
later notation in the file keeps parsing. -/
def parserReferencingKinds : List Name := [
  ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.syntaxAbbrev,
  ``Lean.Parser.Command.macro, ``Lean.Parser.Command.elab]

/-- Wrapper commands and the path to their inner command (`none`: the last argument, looking
through optional/sequence nodes). -/
def wrapperKinds : List (Name × Option (List Nat)) := [
  (``Lean.Parser.Command.in, some [2]),
  (`Mathlib.Tactic.scopedNS, none),
  (`Lean.Elab.Command.commandWith_weak_namespace__, none),
  (`Lean.Parser.Command.withWeakNamespace, none),
  (`commandUnsuppress_compilationIn_, none)]

/-- Path to the last argument, looking through `null` nodes. -/
partial def lastPath (stx : Syntax) : List Nat :=
  let n := stx.getNumArgs
  if n == 0 then [] else
    let i := n - 1
    if stx[i].getKind == nullKind then i :: lastPath stx[i] else [i]

def getPath (stx : Syntax) : List Nat → Syntax
  | [] => stx
  | i :: p => getPath stx[i] p

def setPath (stx : Syntax) : List Nat → Syntax → Syntax
  | [], s => s
  | i :: p, s => stx.setArg i (setPath stx[i] p s)

/-- If `stx` is a wrapper command, its inner command and a function that rebuilds the wrapper
around a replacement inner command. A `choice` node (several parsers accepted the same text) is
resolved to its first alternative. -/
partial def unwrap? (stx : Syntax) : Option (Syntax × (Syntax → Syntax)) := do
  if stx.getKind == choiceKind then
    if stx.getNumArgs == 0 then none else unwrap? stx[0]
  else
    let path? ← wrapperKinds.lookup stx.getKind
    let path := path?.getD (lastPath stx)
    return (getPath stx path, setPath stx path)

/-- Is this a command we elaborate (see `scopingKinds`)? Wrappers are elaborated iff their inner
command is. -/
partial def isScoping (stx : Syntax) (afterFinding : Bool := false) : Bool :=
  match unwrap? stx with
  | some (inner, _) => isScoping inner afterFinding
  | none =>
    let k := stx.getKind
    scopingKinds.contains k && !(afterFinding && parserReferencingKinds.contains k)

/-- A flagged construct at a position. -/
structure Finding where
  pos : String.Pos.Raw
  construct : String
  /-- Extra explanation, used for parse errors and missing imports. -/
  detail : String := ""

/-- Collect all flagged nodes in a syntax tree. -/
partial def walk (stx : Syntax) (acc : Array Finding := #[]) : Array Finding :=
  match stx with
  | .node _ k args =>
    let pos := stx.getPos?.getD 0
    let acc :=
      if let some (_, c) := flaggedKinds.find? (·.1 == k) then acc.push { pos, construct := c }
      else if k == ``Lean.Parser.Attr.simple then
        match flaggedAttrs.find? (·.1 == stx[0].getId) with
        | some (_, c) => acc.push { pos, construct := c }
        | none => acc
      else acc
    args.foldl (fun acc a => walk a acc) acc
  | _ => acc

/-- All identifiers in a syntax tree. -/
partial def identsIn (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .ident _ _ n _ => acc.push n
  | .node _ _ args => args.foldl (fun acc a => identsIn a acc) acc
  | _ => acc

/-- Names mentioned by `open` declarations inside a command (namespaces, and possibly declaration
names in `open Foo (bar)`, which is harmless). -/
partial def openedNamespaces (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .node _ k args =>
    if k == ``Lean.Parser.Command.openSimple || k == ``Lean.Parser.Command.openScoped
        || k == ``Lean.Parser.Command.openOnly || k == ``Lean.Parser.Command.openHiding
        || k == ``Lean.Parser.Command.openRenaming then
      identsIn stx acc
    else args.foldl (fun acc a => openedNamespaces a acc) acc
  | _ => acc

/-- The allowlist: for each path, how many uses of each construct are allowed. -/
abbrev Allowlist := Std.HashMap String (Std.HashMap String Nat)

/-- Normalise a path for use as an allowlist key: forward slashes, no leading `./`. -/
def normalizePath (p : String) : String :=
  let p := p.replace "\\" "/"
  if p.startsWith "./" then (p.drop 2).toString else p

def parseAllowlist (contents : String) : Allowlist := Id.run do
  let mut m : Allowlist := {}
  for line in contents.splitOn "\n" do
    let line := line.trimAscii.toString
    -- whole-line comments only: `#` also starts the construct name `#eval`
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn ":" with
    | [path, constructs] =>
      let mut allowed : Std.HashMap String Nat := {}
      for c in (constructs.splitOn " ").filter (!·.isEmpty) do
        match c.splitOn "=" with
        | [c, n] => allowed := allowed.insert c (n.toNat?.getD 0)
        | _ => allowed := allowed.insert c 1
      m := m.insert (normalizePath path.trimAscii.toString) allowed
    | _ => continue
  return m

structure Config where
  root : FilePath := "."
  allowlistPath : Option FilePath := some ("scripts" / "nolints-exec.txt")
  github : Bool := false
  emit : Bool := false
  jobs : Option Nat := none
  verbose : Bool := false
  files : Array String := #[]

/-- For `macro` and `elab`, the `syntax` command that they would declare, without the macro or
elaborator body. Mirrors `Lean.Elab.Command.elabMacro` and `elabElab`. Returns `none` if the
command has an unexpected shape. -/
def syntaxPartOfMacroOrElab (stx : Syntax) : CommandElabM (Option Syntax) := do
  match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      macro%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
        $cat => $_) =>
    let (stxParts, _) := (← args.mapM expandMacroArg).unzip
    return some <|← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      syntax%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $[$stxParts]* : $cat)
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      elab%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $args:macroArg* :
        $cat $[<= $_]? => $_) =>
    let (stxParts, _) := (← args.mapM expandMacroArg).unzip
    return some <|← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      syntax%$tk$[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $[$stxParts]* : $cat)
  | _ => return none

/-- The command to elaborate for a scoping command: `macro`/`elab` (also inside wrappers) are
replaced by their `syntax` part; `none` if that is not possible, in which case nothing is
elaborated (later uses of the syntax then fail to parse, which is reported). -/
partial def syntaxOnly (stx : Syntax) : CommandElabM (Option Syntax) := do
  match unwrap? stx with
  | some (inner, rebuild) => return (← syntaxOnly inner).map rebuild
  | none =>
    let k := stx.getKind
    if k == ``Lean.Parser.Command.macro || k == ``Lean.Parser.Command.elab then
      syntaxPartOfMacroOrElab stx
    else return some stx

/-- Elaborate a scoping command (see `syntaxOnly`), discarding all messages. Returns the first
error message, if any. -/
def elabScoping (stx : Syntax) : CommandElabM (Option String) := do
  -- `open NS` fails if nothing has created `NS` yet, which happens when `NS` is only created by a
  -- command we do not elaborate (e.g. `scoped[NS] attribute [instance] …` earlier in the file).
  -- Registering the namespace up front is harmless and lets `open scoped NS` activate the
  -- notations later declared in it.
  for ns in openedNamespaces stx do
    if !ns.isAnonymous then modifyEnv (·.registerNamespace ns)
  try
    let some stx ← syntaxOnly stx
      | return some "unexpected shape of `macro`/`elab` command; its syntax was not set up"
    elabCommandTopLevel stx
    let msgs := (← get).messages
    modify fun s => { s with messages := {} }
    match msgs.toList.find? (·.severity == .error) with
    | some m => return some (← m.data.toString)
    | none => return none
  catch e =>
    modify fun s => { s with messages := {} }
    return some (← e.toMessageData.toString)

/-- Start a fresh top-level scope for a file. -/
def resetScopes (opts : Options) : CommandElabM Unit :=
  modify fun s => { s with scopes := [{ header := "", opts }], messages := {} }

/-- Replay the parser-affecting commands of a file (see `scopingKinds`) without recording any
findings. Used for imports whose `.olean` is not available. -/
partial def replay (path : FilePath) (opts : Options) : CommandElabM Unit := do
  let contents ← IO.FS.readFile path
  let ictx := mkInputContext contents path.toString
  let (_, pstate, _) ← parseHeader ictx
  resetScopes opts
  withReader (fun c => { c with fileName := path.toString, fileMap := ictx.fileMap }) do
    let mut pstate := pstate
    repeat
      let s ← get
      let scope := s.scopes.head!
      let pmctx := { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
                     openDecls := scope.openDecls }
      let (cmd, ps, _) := parseCommand ictx pmctx pstate {}
      pstate := ps
      if isTerminalCommand cmd then break
      if isScoping cmd then discard <| elabScoping cmd

/-- Is the `k`-th (1-based) use of `construct` allowed? -/
def allowed (allow : Std.HashMap String Nat) (construct : String) (k : Nat) : Bool :=
  k ≤ allow.getD construct 0

/-- Lint one file: parse every command, walk it for flagged constructs, elaborate the
parser-affecting commands. Returns the findings, each with whether it is allowed. -/
def lintFile (path : FilePath) (opts : Options) (allow : Std.HashMap String Nat)
    (stopOnFinding verbose : Bool) (initial : Array Finding) :
    CommandElabM (Array (Finding × Bool)) := do
  let contents ← IO.FS.readFile path
  let ictx := mkInputContext contents path.toString
  let (_, pstate, hdrMsgs) ← parseHeader ictx
  resetScopes opts
  withReader (fun c => { c with fileName := path.toString, fileMap := ictx.fileMap }) do
    let mut pstate := pstate
    let mut counts : Std.HashMap String Nat := {}
    let mut findings : Array (Finding × Bool) := #[]
    let mut afterFinding := false
    let mut lastElabError : Option (Position × String) := none
    let record (counts : Std.HashMap String Nat) (f : Finding) :
        Std.HashMap String Nat × (Finding × Bool) :=
      let k := counts.getD f.construct 0 + 1
      (counts.insert f.construct k, (f, allowed allow f.construct k))
    for f in initial do
      let (c, r) := record counts f
      counts := c; findings := findings.push r
    for m in hdrMsgs.toList do
      if m.severity == .error then
        let (c, r) := record counts
          { pos := ictx.fileMap.ofPosition m.pos, construct := parseErrorConstruct,
            detail := ← m.data.toString }
        counts := c; findings := findings.push r
    repeat
      let s ← get
      let scope := s.scopes.head!
      let pmctx := { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
                     openDecls := scope.openDecls }
      let (cmd, ps, msgs) := parseCommand ictx pmctx pstate {}
      pstate := ps
      if isTerminalCommand cmd then break
      let mut fs := walk cmd
      for m in msgs.toList do
        if m.severity == .error then
          let mut detail ← m.data.toString
          if let some (p, e) := lastElabError then
            detail := detail ++ s!" (a command at line {p.line} could not be set up: {e})"
          fs := fs.push
            { pos := ictx.fileMap.ofPosition m.pos, construct := parseErrorConstruct, detail }
      for f in fs do
        let (c, r) := record counts f
        counts := c; findings := findings.push r
        if stopOnFinding && !r.2 then afterFinding := true
      if isScoping cmd afterFinding then
        if let some e ← elabScoping cmd then
          let p := ictx.fileMap.toPosition (cmd.getPos?.getD 0)
          if verbose then IO.eprintln s!"{path}:{p.line}: could not set up command: {e}"
          lastElabError := some (p, (e.take 200).toString)
    return findings

/-- Path (relative to the root) of the source of a module, if it exists. -/
def sourceOf (root : FilePath) (mod : Name) : IO (Option FilePath) := do
  let p := modToFilePath root mod "lean"
  return if (← p.pathExists) then some p else none

/-- Compute the imports to load and the files to replay for linting `path`: imports with an
`.olean` on the search path are loaded; the others are replayed from source (transitively), in
dependency order. Imports that are neither are returned as findings. -/
partial def resolveImports (root : FilePath) (path : FilePath) :
    IO (Array Import × Array FilePath × Array Finding) := do
  let sp ← searchPathRef.get
  let rec go (path : FilePath) :
      StateT (Array Import × Array FilePath × Array Finding × NameSet) IO Unit := do
    let contents ← IO.FS.readFile path
    let (hdr, _, _) ← parseHeader (mkInputContext contents path.toString)
    for i in headerToImports hdr do
      if (← get).2.2.2.contains i.module then continue
      modify fun (a, b, c, d) => (a, b, c, d.insert i.module)
      -- `findWithExt` only locates the package root; check that the `.olean` really exists
      if (← (← sp.findWithExt "olean" i.module).mapM (·.pathExists)) == some true then
        modify fun (a, b, c, d) => (a.push i, b, c, d)
      else if let some src ← sourceOf root i.module then
        go src
        modify fun (a, b, c, d) => (a, b.push src, c, d)
      else
        let detail := s!"`{i.module}` (imported by {path}) has no `.olean` and no source"
        let f : Finding := { pos := 0, construct := missingImportConstruct, detail }
        modify fun (a, b, c, d) => (a, b, c.push f, d)
  let ((), (l, r, n, _)) ← (go path).run (#[], #[], #[], {})
  return (l, r, n)

def formatFinding (cfg : Config) (rel : String) (fm : FileMap) (f : Finding) (k : Nat)
    (allowedCount : Nat) : String :=
  let p := fm.toPosition f.pos
  let allowlist := cfg.allowlistPath.getD "the allowlist"
  let msg :=
    if f.construct == parseErrorConstruct then
      s!"could not parse this file: {f.detail}"
    else if f.construct == missingImportConstruct then
      s!"could not resolve an import: {f.detail}"
    else if allowedCount == 0 then
      s!"'{f.construct}' is not allowed here: it executes code at elaboration time or bypasses \
        the type checker. If this use is intended and has been reviewed, add \
        '{rel}: {f.construct}' to {allowlist}."
    else
      s!"this is use number {k} of '{f.construct}' in this file, but only {allowedCount} \
        {if allowedCount == 1 then "is" else "are"} allowed. If this use is intended and has \
        been reviewed, update the count for '{rel}: {f.construct}={allowedCount}' in {allowlist}."
  if cfg.github then
    s!"::error file={rel},line={p.line},col={p.column + 1}::{msg}"
  else
    s!"{rel}:{p.line}:{p.column}: error: {msg}"

/-- Lint a single file in this process. Returns `true` if there were disallowed findings. -/
unsafe def lintSingle (cfg : Config) (rel : String) : IO Bool := do
  let rel := normalizePath rel
  let path := cfg.root / rel
  let allowlist ← do
    match cfg.allowlistPath with
    | some p =>
      let p := cfg.root / p
      if (← p.pathExists) then pure (parseAllowlist (← IO.FS.readFile p)) else pure {}
    | none => pure {}
  let allow := allowlist.getD rel {}
  let (imports, toReplay, importFindings) ← resolveImports cfg.root path
  enableInitializersExecution
  let env ← importModules imports {} (loadExts := true)
  let opts := ((Options.empty.setBool `Elab.async false).setBool `quotPrecheck false)
    |>.setBool `linter.all false
  let ctx : Command.Context :=
    { fileName := rel, fileMap := default, snap? := none, cancelTk? := none }
  let act : CommandElabM (Array (Finding × Bool)) := do
    for src in toReplay do replay src opts
    lintFile path opts allow (stopOnFinding := !cfg.emit) (verbose := cfg.verbose) importFindings
  let findings ← match ← ((act ctx).run' (Command.mkState env {} opts)).toIO' with
    | .ok fs => pure fs
    | .error e => throw <| IO.userError (← e.toMessageData.toString)
  let fm := (mkInputContext (← IO.FS.readFile path) rel).fileMap
  if cfg.emit then
    let mut counts : Std.HashMap String Nat := {}
    for (f, _) in findings do counts := counts.insert f.construct (counts.getD f.construct 0 + 1)
    if !counts.isEmpty then
      let entries := counts.toArray.qsort (·.1 < ·.1) |>.map fun (c, n) => s!"{c}={n}"
      IO.println s!"{rel}: {" ".intercalate entries.toList}"
    return false
  let mut bad := false
  let mut counts : Std.HashMap String Nat := {}
  for (f, ok) in findings do
    let k := counts.getD f.construct 0 + 1
    counts := counts.insert f.construct k
    if !ok then
      bad := true
      IO.println (formatFinding cfg rel fm f k (allow.getD f.construct 0))
  return bad

/-- Child processes: we read their stdout, they inherit our stderr. -/
def childCfg : IO.Process.StdioConfig := { stdout := .piped, stdin := .null, stderr := .inherit }

/-- Run one child process per file, `jobs` at a time, forwarding their output. -/
def lintAll (cfg : Config) (args : List String) : IO Bool := do
  let jobs ← match cfg.jobs with
    | some n => pure (max n 1)
    | none =>
      -- `nproc` is not available everywhere (e.g. macOS); fall back to a fixed number.
      let nproc ← (do return (← IO.Process.run { cmd := "nproc" }).trimAscii.toString.toNat?)
        |>.toBaseIO
      pure <| (nproc.toOption.bind id |>.getD 4).max 1
  let app ← IO.appPath
  let mut bad := false
  let mut pending := cfg.files.toList
  let mut running : Array (String × IO.Process.Child childCfg) := #[]
  while !pending.isEmpty || !running.isEmpty do
    while running.size < jobs && !pending.isEmpty do
      let f := pending.head!
      pending := pending.tail
      let spawnArgs : IO.Process.SpawnArgs :=
        { toStdioConfig := childCfg, cmd := app.toString, args := #["--single", f] ++ args.toArray }
      match ← (IO.Process.spawn spawnArgs).toBaseIO with
      | .ok child => running := running.push (f, child)
      | .error e =>
        bad := true
        IO.println s!"{f}: error: could not start lint-exec: {e}"
    -- wait for the oldest running child
    let some (f, child) := running[0]? | break
    running := running.eraseIdx! 0
    let out ← child.stdout.readToEnd
    let code ← child.wait
    IO.print out
    if code != 0 then
      bad := true
      if out.isEmpty then
        IO.println s!"{f}: error: lint-exec exited with code {code}"
  return bad

/-- Parse the command line: the configuration, whether this is a `--single` child, and the
options to pass on to children. -/
def parseArgs (args : List String) : IO (Except String (Config × Bool × List String)) := do
  let mut cfg : Config := {}
  let mut single := false
  let mut passthrough : List String := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--single" :: r => single := true; rest := r
    | "--verbose" :: r =>
      cfg := { cfg with verbose := true }
      passthrough := passthrough ++ ["--verbose"]; rest := r
    | "--github" :: r =>
      cfg := { cfg with github := true }
      passthrough := passthrough ++ ["--github"]; rest := r
    | "--emit-allowlist" :: r =>
      cfg := { cfg with emit := true }
      passthrough := passthrough ++ ["--emit-allowlist"]; rest := r
    | "--no-allowlist" :: r =>
      cfg := { cfg with allowlistPath := none }
      passthrough := passthrough ++ ["--no-allowlist"]; rest := r
    | "--root" :: d :: r =>
      cfg := { cfg with root := d }
      passthrough := passthrough ++ ["--root", d]; rest := r
    | "--allowlist" :: p :: r =>
      cfg := { cfg with allowlistPath := some p }
      passthrough := passthrough ++ ["--allowlist", p]; rest := r
    | "--files-from" :: p :: r =>
      let lines := (← IO.FS.readFile p).splitOn "\n" |>.map (·.trimAscii.toString)
        |>.filter (!·.isEmpty) |>.map normalizePath
      cfg := { cfg with files := cfg.files ++ lines.toArray }; rest := r
    | "--jobs" :: n :: r =>
      let some n := n.toNat? | return .error s!"--jobs expects a number, got '{n}'"
      cfg := { cfg with jobs := some n }; rest := r
    | f :: r =>
      if f.startsWith "--" then return .error s!"unknown option '{f}'"
      cfg := { cfg with files := cfg.files.push (normalizePath f) }; rest := r
    | [] => pure ()
  return .ok (cfg, single, passthrough)

end LintExec

open LintExec in
unsafe def main (args : List String) : IO UInt32 := do
  match ← parseArgs args with
  | .error e =>
    IO.eprintln s!"lint-exec: {e}"
    return 2
  | .ok (cfg, single, passthrough) =>
    initSearchPath (← findSysroot)
    if single then
      let some f := cfg.files[0]? | IO.eprintln "lint-exec: --single needs a file"; return 2
      return if (← lintSingle cfg f) then 1 else 0
    else
      return if (← lintAll cfg passthrough) then 1 else 0
