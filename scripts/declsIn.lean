import Std
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.BinaryHeap
import Mathlib.Lean.CoreM

open Lean

/-- Given an array of modules, this function returns the sorted list of all non-blacklisted
declarations provided by those modules. -/
def getDeclsInPackagesNoBlacklist (pkgs : Array Name) : CoreM (Array Name) := do
  let arr_decls ← pkgs.mapM fun pkg => do
    (← Std.Tactic.Lint.getDeclsInPackage pkg).filterM (Functor.map (! ·) ∘ Lean.Name.isBlackListed)
  return arr_decls.flatten.heapSort (toString · < toString ·) |>.deduplicateSorted

def main (args : List String) : IO UInt32 := do
  let modules : Array Name ← match args with
  | [] => pure #[]
  | args => args.toArray.mapM (Lean.moduleNameOfFileName ⟨·⟩ .none)
  CoreM.withImportModules modules (searchPath := compile_time_search_path%) do
    let decls ← getDeclsInPackagesNoBlacklist modules
    for decl in decls do
      IO.println decl
  return 0
