import Lean.Server.References
import Lean.DocString
import Lean
import Std.Tactic.OpenPrivate

open private builtinDocStrings docStringExt from Lean.DocString

open Lean Elab PrettyPrinter
def failWith {α} (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode

def modPrefixes : List Name := [`Init, `Lean]

def act' (fileNames : List String) : CoreM Unit := do
  let env ← getEnv
  let builtinDocStrings ← builtinDocStrings.get
  let mut counts := HashMap.empty
  for fileName in fileNames do
    let ilean ← Lean.Server.Ilean.load fileName
    counts := ilean.references.fold (init := counts)
      fun counts refident info => Id.run do
        let .const mod n := refident | return counts
        unless modPrefixes.any (·.isPrefixOf mod) do return counts
        if (docStringExt.find? env n).isSome then return counts
        if (builtinDocStrings.find? n).isSome then return counts
        if let some ci := env.find? n then
          if ci matches .thmInfo .. then return counts
        return counts.insert (mod,n) (counts.findD (mod,n) 0 + info.usages.size)

  counts.toArray.qsort (·.2 > ·.2) |>.forM fun ((mod,n), count) =>
    IO.println s!"{mod},{n},{count}"

instance : ToExpr System.FilePath where
  toTypeExpr := Lean.mkConst ``System.FilePath
  toExpr path := mkApp (Lean.mkConst ``System.FilePath.mk) (toExpr path.1)

elab "#compileTimeSearchPath" : term => do
  let path ← searchPathRef.get
  return toExpr path
def compileTimeSearchPath : SearchPath := #compileTimeSearchPath


unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then failWith "Usage: occCount [file.ilean ..]"

  initSearchPath (← findSysroot)
  let imports := #[{module := `Mathlib}]
  withImportModules imports {} 0 fun env => do
    let ctx := {fileName := "/", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> (act' args).toIO ctx state
