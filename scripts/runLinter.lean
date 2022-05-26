import Mathlib

open Lean in
private abbrev NoLints := Array (Name × Name)

open Lean in
private def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let inst : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|<- liftExcept <| Json.parse <|<- IO.FS.readFile path

open Lean in
private def writeJsonFile (α) [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

local elab "#runLinters" update:(&"update")? : command =>
  open Lean Elab Command Mathlib.Tactic.Lint in do
  let nolintsFile := "scripts/nolints.json"
  let nolints ← readJsonFile NoLints nolintsFile
  let decls ← liftCoreM getDeclsInMathlib
  let linters ← liftCoreM (getChecks (slow := true) (extra := []) (useOnly := false))
  let results ← liftCoreM (lintCore decls linters.toArray)
  if update.isSome then
    writeJsonFile NoLints nolintsFile <|
      .qsort (lt := fun (a,b) (c,d) => a.lt c || (a == c && b.lt d)) <|
      .flatten <| results.map fun (linter, decls) =>
      decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
  let results := results.map fun (linter, decls) =>
    .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
      if linter.name == linter' then decls.erase decl' else decls
  let failed := results.any (!·.2.isEmpty)
  if failed then
    let fmtResults ← liftCoreM do
      formatLinterResults results decls (groupByFilename := true)
        "in mathlib" (runSlowLinters := true) .medium linters.length
    logError fmtResults
  else
    logInfo "-- Linting passed."

#runLinters
-- update
