import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Batteries.Lean.Util.Path

/-!
Michael's fork of the batteries `runLinter` script:
allow configuring which linters to run, as an experiment.
-/
open Lean Core Elab Command Std.Tactic.Lint
open System (FilePath)

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ ↦ x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

/--
Usage: `runLinter [--update] [Mathlib.Data.List.Basic]`

Runs the linters on all declarations in the given module (or `Mathlib` by default).
If `--update` is set, the `nolints` file is updated to remove any declarations that no longer need
to be nolinted.

If the `--only` flag is passed, only a given set of linters is applied.
(In conjunction with the `--update` flag, this could lead to the nolints file being shorter
 than expected; use with care!)
-/
unsafe def main (args : List String) : IO Unit := do
  let (update, args) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  let some module :=
      match args with
      | [] => some `Mathlib
      | [mod] => match mod.toName with
        | .anonymous => none
        | name => some name
      | _ => none
    | IO.eprintln "Usage: runLinter [--update] [Mathlib.Data.List.Basic]" *> IO.Process.exit 1
  searchPathRef.set compile_time_search_path%
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    -- run `lake build module` (and ignore result) if the file hasn't been built yet
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{module}"]
      stdin := .null
    }
    _ ← child.wait
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  withImportModules #[{module}] {} (trustLevel := 1024) fun env ↦
    let ctx := { fileName := "", fileMap := default }
    let state := { env }
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let decls ← getDeclsInPackage module.getRoot
      let linters ← getChecks (slow := true) (useOnly := false)
      let results ← lintCore decls linters
      if update then
        writeJsonFile (α := NoLints) nolintsFile <|
          .qsort (lt := fun (a, b) (c, d) ↦ a.lt c || (a == c && b.lt d)) <|
          .flatten <| results.map fun (linter, decls) ↦
          decls.fold (fun res decl _ ↦ res.push (linter.name, decl)) #[]
      let results := results.map fun (linter, decls) ↦
        .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') ↦
          if linter.name == linter' then decls.erase decl' else decls
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
            s!"in {module}" (runSlowLinters := true) .medium linters.size
        IO.print (← fmtResults.toString)
        IO.Process.exit 1
      else
        IO.println "-- Linting passed."
