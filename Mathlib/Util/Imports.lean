/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Lean.Expr.Basic

/-!
# Tools for analyzing imports.

Provides the command `#redundant_imports` which
lists any transitively redundant imports in the current module.

## Future work
By inspecting the declarations and syntax in the current file,
we can suggest a minimal set of imports.
-/

open Lean

namespace Lean.Environment

/--
Find the imports of a given module.
-/
def importsOf (env : Environment) (n : Name) : Array Name :=
  if n = env.header.mainModule then
    env.header.imports.map Import.module
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports.map Import.module |>.erase `Init
    | .none => #[]

/--
Construct the import graph of the current file.
-/
partial def importGraph (env : Environment) : NameMap (Array Name) :=
  let main := env.header.mainModule
  let imports := env.header.imports.map Import.module
  imports.foldl (fun m i => process env i m) (({} : NameMap _).insert main imports)
    |>.erase Name.anonymous
where
  process (env) (i) (m) : NameMap (Array Name) :=
    if m.contains i then
      m
    else
      let imports := env.importsOf i
      imports.foldr (fun i m => process env i m) (m.insert i imports)

/--
Return the redundant imports (i.e. those transitively implied by another import)
amongst a candidate list of imports.
-/
partial def findRedundantImports (env : Environment) (imports : Array Name) : NameSet :=
  let run := visit env.importGraph imports
  let (_, seen) := imports.foldl (fun ⟨v, s⟩ n => run v s n) ({}, {})
  seen
where
  visit (Γ) (targets) (visited) (seen) (n) : NameSet × NameSet :=
    if visited.contains n then
      (visited, seen)
    else
      let imports := (Γ.find? n).getD #[]
      let (visited', seen') := imports.foldl (fun ⟨v, s⟩ t => visit Γ targets v s t) (visited, seen)
      (visited'.insert n,
        imports.foldl (fun s t => if targets.contains t then s.insert t else s) seen')

end Lean.Environment

namespace Lean.NameMap

/--
Compute the transitive closure of an import graph.
-/
partial def transitiveClosure (m : NameMap (Array Name)) : NameMap NameSet :=
  m.fold (fun r n i => process r n i) {}
where
  process (r : NameMap NameSet) (n : Name) (i : Array Name) : NameMap NameSet :=
    if r.contains n then
      r
    else
      let r' := i.foldr (fun i r => process r i ((m.find? i).getD #[])) r
      let t := i.foldr
        (fun j s => ((r'.find? j).getD {}).fold NameSet.insert s)
        (RBTree.ofList i.toList)
      r'.insert n t

/--
Compute the transitive reduction of an import graph.

Typical usage is `transitiveReduction (← importGraph)`.
-/
def transitiveReduction (m : NameMap (Array Name)) : NameMap (Array Name) :=
  let c := transitiveClosure m
  m.fold (fun r n a =>
    r.insert n (a.foldr (fun i b => b.filter (fun j => ! ((c.find? i).getD {}).contains j)) a)) {}

/-- Restrict an import graph to only the downstream dependencies of some set of modules. -/
def dependenciesOf (m : NameMap (Array Name)) (targets : NameSet) : NameMap (Array Name) :=
  let tc := transitiveClosure m
  let P (n : Name):= targets.contains n || ((tc.find? n).getD {}).any fun j => targets.contains j
  m.fold (init := {}) fun r n i =>
    if P n then
      r.insert n (i.filter P)
    else
      r

end Lean.NameMap

/--
Return the redundant imports (i.e. those transitively implied by another import)
of a specified module (or the current module if `none` is specified).
-/
def redundantImports (n? : Option Name := none) : CoreM NameSet := do
  let env ← getEnv
  let imports := env.importsOf (n?.getD (env.header.mainModule))
  return env.findRedundantImports imports

/--
List the imports in this file which can be removed
because they are transitively implied by another import.
-/
elab "#redundant_imports" : command => do
  let redundant := (← Elab.Command.liftCoreM do redundantImports)
  if redundant.isEmpty then
    logInfo "No transitively redundant imports found."
  else
    logInfo <| "Found the following transitively redundant imports:\n" ++
      m!"{Format.joinSep redundant.toList "\n"}"

/--
Return the names of the modules in which constants used in the current file were defined,
with modules already transitively imported removed.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Lean.Environment.minimalRequiredModules (env : Environment) : Array Name :=
  let required := env.requiredModules.toArray
  let redundant := findRedundantImports env required
  required.filter fun n => ¬ redundant.contains n

/--
Try to compute a minimal set of imports for this file,
by analyzing the declarations.

This must be run at the end of the file,
and is not aware of syntax and tactics,
so the results will likely need to be adjusted by hand.
-/
elab "#minimize_imports" : command => do
  let imports := (← getEnv).minimalRequiredModules.qsort Name.lt
    |>.toList.map (fun n => "import " ++ n.toString)
  logInfo <| Format.joinSep imports "\n"

/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
-/
def Lean.Name.findHome (n : Name) : CoreM NameSet := do
  let required ← n.requiredModules
  let imports := (← getEnv).importGraph.transitiveClosure
  let mut candidates : NameSet := {}
  for (n, i) in imports do
    if required.all fun r => n == r || i.contains r then
      candidates := candidates.insert n
  for c in candidates do
    for i in candidates do
      if imports.find? i |>.getD {} |>.contains c then
        candidates := candidates.erase i
  return candidates

open Elab in
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
-/
elab "#find_home" n:ident : command => do
  let n ← resolveGlobalConstNoOverloadWithInfo n
  for i in (← Elab.Command.liftCoreM do n.findHome) do
    logInfo i
