import Std.Tactic.Lint
import Std.Lean.Util.Path
import Mathlib.Lean.CoreM

open Lean Core Elab Command Std.Tactic.Lint

abbrev NoLints := Array (Name × Name)

def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

def writeJsonFile (α) [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

unsafe def main (args : List String) : IO Unit := do
  let (update, args) :=
    match args with
    | "--update" :: args => (true, args)
    | _ => (false, args)
  let some module :=
      match args with
      | [] => some `Mathlib
      | [mod] => Syntax.decodeNameLit s!"`{mod}"
      | _ => none
    | IO.eprintln "Usage: runMathlibLinter [--update] [Mathlib.Data.Nat.Basic]" *> IO.Process.exit 1
  let nolintsFile := "scripts/nolints.json"
  let nolints ← readJsonFile NoLints nolintsFile
  CoreM.withImportModules #[module]
      (searchPath := compile_time_search_path%) (trustLevel := 1024) do
    let decls ← getDeclsInPackage `Mathlib
    let linters ← getChecks (slow := true) (useOnly := false)
    let results ← lintCore decls linters
    if update then
      writeJsonFile NoLints nolintsFile <|
        .qsort (lt := fun (a,b) (c,d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
        decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true)
          "in mathlib" (runSlowLinters := true) (useErrorFormat := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.print "-- Linting passed."
