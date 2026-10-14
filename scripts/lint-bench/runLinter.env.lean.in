import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

open Lake

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  -- load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"

  -- build an array of all root modules of `lean_exe` and `lean_lib` default targets
  let defaultTargetModules ← workspace.root.defaultTargets.flatMapM fun target => do
    if let some lib := workspace.root.findLeanLib? target then
      pure <| (← lib.getModuleArray).map Lake.Module.name
    else if let some exe := workspace.root.findLeanExe? target then
      pure #[exe.config.root]
    else
      pure #[]
  return defaultTargetModules

/-- Arguments for `runLinter`. -/
structure LinterConfig where
  /-- Whether to update nolints. Default is `false`; set to `true` with `--update`. -/
  updateNoLints : Bool := false
  /-- Whether to throw an error if necessary oleans are not already present (as opposed to building
  them). Default is `false`; set to `true` with `--no-build`. -/
  noBuild : Bool := false
  /-- Whether to enable tracing. Default is `false`; set to `true` with `--trace` or `-v`. -/
  trace := false
  /-- If set (with `--only-modules=FILE`), a file listing module names, one per line. Local linters
  (`Linter.isLocal`) then lint only the declarations defined in those modules; the other linters
  still lint everything. -/
  onlyModules : Option System.FilePath := none

@[always_inline, inline]
private def Except.consError (e : ε) : Except (List ε) α → Except (List ε) α
  | Except.error errs => Except.error <| e :: errs
  | Except.ok _       => Except.error [e]

/--
Parse args list for `runLinter` and return the config and specified module arguments. Default
config settings are determined by the default values for fields of `LinterConfig`.

Throws an exception if unable to parse the arguments.
Returns `none` for the specified module if no modules are specified.-/
def parseLinterArgs (args : List String) :
    Except (List String) (LinterConfig × List Name) :=
  go {} [] args
where
  /-- Traverses the list, handling the non-flag elements as modules and erroring if parsing fails. -/
  go (parsed : LinterConfig) (mods: List Name) : List String → Except (List String) (LinterConfig × List Name)
    | arg :: rest =>
      if let some parsed := parseArg parsed arg then
        go parsed mods rest
      else
        match arg.toName with
        | .anonymous => Except.error [s!"could not parse argument '{arg}'"]
        | mod => go parsed (mod :: mods) rest
    | [] => Except.ok (parsed, mods.reverse)

  /-- Parses a single config argument. -/
  parseArg (parsed : LinterConfig) : String → Option LinterConfig
    | "--update"   => some { parsed with updateNoLints := true }
    | "--no-build" => some { parsed with noBuild := true }
    | "--trace"
    | "-v"         => some { parsed with trace := true }
    | arg =>
      if let some file := arg.dropPrefix? "--only-modules=" then
        if file.isEmpty then none else some { parsed with onlyModules := some file.toString }
      else none

/--
Return an array of the modules to lint.

If `specifiedModules` is not empty, return an array containing only `specifiedModule`.
Otherwise, resolve the default root modules from the Lake workspace. -/
def determineModulesToLint (specifiedModules : List Name) : IO (Array Name) := do
  match specifiedModules with
  | [] =>
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules
  | modules =>
    println!"Running linter on specified modules: {modules}"
    return modules.toArray

/--
Run the Batteries linter on a given module and update the linter if `update` is `true`.
If `leakEnv` is `true`, mark the imported environment as persistent.
-/
unsafe def runLinterOnModule (cfg : LinterConfig) (module : Name)
    (leakEnv := false) : IO Unit := do
  let { updateNoLints, noBuild, trace, onlyModules } := cfg
  if updateNoLints && onlyModules.isSome then
    IO.eprintln "--update cannot be combined with --only-modules: \
      it would rewrite the nolints file from a partial run"
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  let rec
    /-- Builds `module` if the filepath `olean` does not exist. Throws if olean is not found and
    `noBuild := true`. -/
    buildIfNeeded (module : Name) : IO Unit := do
      let olean ← findOLean module
      unless (← olean.pathExists) do
        if noBuild then
          IO.eprintln s!"[{module}] Could not find olean for module `{module}` at given path:\n  \
            {olean}"
          IO.Process.exit 1
        else
          if trace then
            IO.println s!"[{module}] Could not find olean for module `{module}` at given path:\n  \
              {olean}\n\
              [{module}] Building `{module}`."
          -- run `lake build +module` (and ignore result) if the file hasn't been built yet
          let child ← IO.Process.spawn {
            cmd := (← IO.getEnv "LAKE").getD "lake"
            args := #["build", s!"+{module}"]
            stdin := .null
          }
          _ ← child.wait
          -- No need to trace on completion, lake's "Build completed successfully" reaches stdout

  buildIfNeeded module
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  buildIfNeeded lintModule
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024)
    (loadExts := true) (leakEnv := leakEnv)
  let mut opts : Options := {}
  -- Propagate `trace` to `CoreM`
  if trace then
    opts := opts.setBool `trace.Batteries.Lint true
  let ctx := {
    fileName := ""
    fileMap := default
    options := opts  }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    traceLint s!"Starting lint..." (inIO := true) (currentModule := module)
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let localDecls ← match onlyModules with
      | none => pure none
      | some file =>
        let env ← getEnv
        let listed := (← IO.FS.lines file).map (·.trimAscii.copy) |>.filter (!·.isEmpty)
          |>.map (·.toName)
        -- Modules that are not in the environment (for example, deleted files) are skipped, but
        -- always reported: a typo would otherwise silently narrow the lint.
        let missing := listed.filter (env.getModuleIdx? · |>.isNone)
        unless missing.isEmpty do
          IO.println s!"[{module}] --only-modules: {missing.size} listed module(s) are not in the \
            environment and are skipped: {missing.toList}"
        let idxs := listed.filterMap env.getModuleIdx?
        let restricted := decls.filter fun d => (env.getModuleIdxFor? d).any idxs.contains
        let nLocal := (linters.filter (·.isLocal)).size
        IO.println s!"[{module}] --only-modules: {nLocal} local linters lint the \
          {restricted.size} declarations of {idxs.size} listed modules; the other \
          {linters.size - nLocal} lint all {decls.size} declarations."
        pure (some restricted)
    let results ← lintCore decls linters (inIO := true) (currentModule := module)
      (localDecls := localDecls)
    if updateNoLints then
      traceLint s!"Updating nolints file at {nolintsFile}" (inIO := true) (currentModule := module)
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    if trace then
      let mut nolintTally : Std.HashMap Name Nat := {}
      for (linter, _) in nolints do
        nolintTally := nolintTally.alter linter fun
          | none   => some 1
          | some n => some (n+1)
      let msgs := nolintTally.toList.map fun (linter, n) => s!"{linter}: {n}"
      IO.println s!"[{module}] {nolintsFile} summary (number of nolints per linter):\n  \
        {"\n  ".intercalate msgs}"
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}{match localDecls with
            | some ds => s!" (local linters: only the {ds.size} declarations of the listed modules)"
            | none => ""}"
          (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

/--
Usage: `runLinter [--update] [--trace | -v] [--no-build] [--only-modules=FILE]
  [Batteries.Data.Nat.Basic]...`

Runs the linters on all declarations in the given modules
(or all root modules of Lake `lean_lib` and `lean_exe` default targets if no module is specified).

If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.

If `--trace` (or, synonymously, `-v`) is set, tracing will be enabled and logged to stdout.

If `--no-build` is set, `runLinter` will throw if either the oleans to be linted or the oleans
which drive the linting itself are not present.

If `--only-modules=FILE` is set, where `FILE` lists module names one per line, local linters
(`Linter.isLocal`) lint only the declarations defined in those modules, for example to lint only
the files a pull request changed; the other linters, such as `simpNF`, still lint every
declaration. Listed modules that are not in the environment are skipped and reported.
`--only-modules` cannot be combined with `--update`. It is only sound for changes to ordinary
modules: a caller must lint everything when a linter's own code or `nolints.json` changes.
-/
unsafe def main (args : List String) : IO Unit := do
  let linterArgs := parseLinterArgs args
  let (cfg, mods) ← match linterArgs with
    | Except.ok args => pure args
    | Except.error msgs => do
      IO.eprintln s!"Error parsing args:\n  {"\n  ".intercalate msgs}"
      IO.eprintln "Usage: \
        runLinter [--update] [--trace | -v] [--no-build] [--only-modules=FILE] \
        [Batteries.Data.Nat.Basic]..."
      IO.Process.exit 1

  let modulesToLint ← determineModulesToLint mods

  -- A single imported environment lives until process exit. Mark it persistent to avoid
  -- atomic reference-count updates when the lint workers share it.
  -- With several modules, each environment must be freed before the next import.
  let leakEnv := modulesToLint.size == 1
  modulesToLint.forM fun module => runLinterOnModule cfg module (leakEnv := leakEnv)
  -- TODO: Remove manual Process.exit
  -- We are doing this to shortcut around a race in Lean's IO finalizers that we have observed in Mathlib CI
  -- (https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/slow.20linting.20step.20CI.3F/with/568830914)
  IO.Process.exit 0
