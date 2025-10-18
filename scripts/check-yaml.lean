/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Lean.CoreM
import Mathlib.Tactic.ToExpr

/-! # Script to check `undergrad.yaml`, `overview.yaml`, `100.yaml` and `1000.yaml`

This assumes `yaml_check.py` has first translated these to `json` files.

It verifies that the referenced declarations exist, and prints an error otherwise.
-/

open IO.FS Lean Lean.Elab
open Lean Core Elab Command

abbrev DBFile := Array (String × Name)

def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

def databases : List String :=
  ["undergrad", "overview", "100", "1000"]

def processDb (decls : ConstMap) : String → IO Bool
| file => do
  let lines ← readJsonFile DBFile s!"{file}.json"
  let missing := lines.filter (fun l ↦ !(decls.contains l.2))
  if 0 < missing.size then
    IO.println s!"Entries in `docs/{file}.yaml` refer to {missing.size} declaration(s) that don't exist. \
      Please correct the following:"
    for p in missing do
      IO.println s!"  {p.1}: {p.2}"
    IO.println ""
    return true
  else
    return false

unsafe def main : IO Unit := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  CoreM.withImportModules #[`Mathlib, `Archive]
      (searchPath := searchPath) (trustLevel := 1024) do
    let decls := (← getEnv).constants
    let results ← databases.mapM (fun p ↦ processDb decls p)
    if results.any id then
      IO.Process.exit 1
