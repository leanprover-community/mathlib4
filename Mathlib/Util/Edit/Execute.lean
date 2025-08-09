import Mathlib.Util.Edit.Extension

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let env ← importModules #[{module := `Mathlib}] {} (loadExts := true)
  executeEdits env `Mathlib
