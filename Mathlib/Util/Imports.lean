/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Command

/-!
# Tools for analyzing imports.

Provides the command `#redundant_imports` which
lists any transitively redundant imports in the current module.

## Future work
By inspecting the declarations and syntax in the current file,
we can suggest a minimal set of imports.
-/

open Lean Meta

namespace Lean.Environment

/--
Find the imports of a given module.
-/
def importsOf (env : Environment) (n : Name) : Array Name :=
  if n = env.header.mainModule then
    env.header.imports.map Import.module
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports.map Import.module
    | .none => #[]

/--
Construct the import graph of the current file.
-/
partial def importGraph (env : Environment) : NameMap (Array Name) :=
  let main := env.header.mainModule
  let imports := env.header.imports.map Import.module
  imports.foldl (fun m i => process env i m) (({} : NameMap _).insert main imports)
where
  process (env) (i) (m) : NameMap (Array Name) :=
    if m.contains i then
      m
    else
      let imports := env.importsOf i
      imports.foldr (fun i m => process env i m) (m.insert i imports)

end Lean.Environment

/--
Return the redundant imports (i.e. those transitively implied by another import)
of a specified module (or the current module if `none` is specified).
-/
def redundantImports (n? : Option Name := none) : MetaM (List Name) := do
  let env ← getEnv
  let imports := env.importsOf (n?.getD ((← getEnv).header.mainModule)) |>.erase `Init
  let run := visit env.importGraph imports
  let (_, seen) := imports.foldl (fun ⟨v, s⟩ n => run v s n) ({}, {})
  return seen.toList
where
  visit (graph) (targets) (visited) (seen) (n) : NameSet × NameSet := Id.run do
    if visited.contains n then
      (visited, seen)
    else
      let imports := (graph.find? n).getD #[]
      (visited.insert n,
        targets.foldl (fun s t => if imports.contains t then s.insert t else s) seen)

/--
List the imports in this file which can be removed
because they are transitively implied by another import.
-/
elab "#redundant_imports" : command => do
  let redundant := (← Elab.Command.liftCoreM <| MetaM.run' do redundantImports)
  if redundant.isEmpty then
    logInfo "No transitively redundant imports found."
  else
    logInfo m!"Found the following transitively redundant imports:\n{Format.joinSep redundant "\n"}"
