/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Thomas R. Murrills
-/
module

import Lean.Data.Json
import Lean.Linter.Deprecated

/-! # Script to check `undergrad.yaml`, `overview.yaml`, `100.yaml` and `1000.yaml`

This assumes `yaml_check.py` has first translated these to `json` files.

It verifies that the referenced declarations exist, and prints an error otherwise.
-/

open Lean

abbrev DBFile := Array (String × Name)

def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

def databases : List String :=
  ["undergrad", "overview", "100", "1000"]

def processDb (env : Environment) (file : String) : IO Bool := do
  let lines ← readJsonFile DBFile s!"{file}.json"
  let mut missing := #[]; let mut deprecated := #[]
  for entry@(_, decl) in lines do
    if !env.contains decl then
      missing := missing.push entry
    else if let some newName := Linter.getDeprecatedNewName env decl then
      deprecated := deprecated.push (entry, newName)
  unless missing.isEmpty do
    IO.println s!"Entries in `docs/{file}.yaml` refer to {missing.size} declaration(s) that don't \
      exist. Please correct the following:"
    for (key, decl) in missing do
      IO.println s!"  {key}: '{decl}'"
  unless deprecated.isEmpty do
    IO.println s!"Entries in `docs/{file}.yaml` refer to {deprecated.size} declaration(s) that are \
      deprecated. Please update the document to refer to the following declaration(s):"
    for ((key, decl), newName) in deprecated do
      IO.println s!"  {key}: '{newName}' (previously '{decl}')"
  return missing.isEmpty && deprecated.isEmpty

public unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[`Mathlib, `Archive] ∅ (trustLevel := 1024) fun env => do
    let results ← databases.mapM (fun p ↦ processDb env p)
    unless results.all id do
      IO.Process.exit 1
