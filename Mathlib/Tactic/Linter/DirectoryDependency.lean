/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Lean.Elab.Command
import Lean.Elab.ParseImportsFast

/-! # The `directoryDependency` linter

The `directoryDependency` linter detects imports between directories that are supposed to be
independent. By specifying that one directory does not import from another, we can improve the
modularity of Mathlib.
-/

/-- Find the longest prefix of `n` such that `f` returns `some` (or return `none` otherwise). -/
def Lean.Name.findPrefix {α} (f : Name → Option α) (n : Name) : Option α := do
  f n <|> match n with
    | anonymous => none
    | str n' _ => n'.findPrefix f
    | num n' _ => n'.findPrefix f

/-- Make a `NameSet` containing all prefixes of `n`. -/
def Lean.Name.prefixes (n : Name) : NameSet :=
  NameSet.insert (n := n) <| match n with
    | anonymous => ∅
    | str n' _ => n'.prefixes
    | num n' _ => n'.prefixes

/-- Collect all prefixes of names in `ns` into a single `NameSet`. -/
def Lean.Name.collectPrefixes (ns : Array Name) : NameSet :=
  ns.foldl (fun ns n => ns.union n.prefixes) ∅

/-- Find a name in `ns` that starts with prefix `p`. -/
def Lean.Name.prefixToName (p : Name) (ns : Array Name) : Option Name :=
  ns.find? p.isPrefixOf

/-- Find the dependency chain, starting at a module that imports `imported`, and ends with the
current module. -/
def Lean.Environment.importPath (env : Environment) (imported : Name) : Array Name := Id.run do
  let mut result := #[]
  let modData := env.header.moduleData
  let modNames := env.header.moduleNames
  if let some idx := env.getModuleIdx? imported then
    let mut target := imported
    for i in [idx.toNat + 1 : modData.size] do
      if modData[i]!.imports.any (·.module == target) then
        target := modNames[i]!
        result := result.push modNames[i]!
  return result

namespace Mathlib.Linter

open Lean Elab Command

/--
The `directoryDependency` linter detects detects imports between directories that are supposed to be
independent. If this is the case, it emits a warning.
-/
register_option linter.directoryDependency : Bool := {
  defValue := true
  descr := "enable the directoryDependency linter"
}

namespace DirectoryDependency

/-- `NamePrefixRel` is a datatype for storing relations between name prefixes.

That is, `R : NamePrefixRel` is supposed to answer given names `(n₁, n₂)` whether there are any
prefixes `n₁'` of `n₁` and `n₂'` of `n₂` such that `n₁' R n₂'`.

The current implementation is a `NameMap` of `NameSet`s, testing each prefix of `n₁` and `n₂` in
turn. This can probably be optimized.
-/
def NamePrefixRel := NameMap NameSet

namespace NamePrefixRel

instance : EmptyCollection NamePrefixRel := inferInstanceAs (EmptyCollection (NameMap _))

/-- Make all names with prefix `n₁` related to names with prefix `n₂`. -/
def insert (r : NamePrefixRel) (n₁ n₂ : Name) : NamePrefixRel :=
  match r.find? n₁ with
    | some ns => NameMap.insert r n₁ (ns.insert n₂)
    | none => NameMap.insert r n₁ (.insert ∅ n₂)

/-- Convert an array of prefix pairs to a `NamePrefixRel`. -/
def ofArray (xs : Array (Name × Name)) : NamePrefixRel :=
  xs.foldl (init := ∅)
    fun r (n₁, n₂) => r.insert n₁ n₂

/-- Get a prefix of `n₁` that is related to a prefix of `n₂`. -/
def find (r : NamePrefixRel) (n₁ n₂ : Name) : Option (Name × Name) :=
  n₁.findPrefix fun n₁' => do
    let ns ← r.find? n₁'
    n₂.findPrefix fun n₂' =>
      if ns.contains n₂'
      then (n₁', n₂')
      else none

/-- Get a prefix of `n₁` that is related to any prefix of the names in `ns`; return the prefixes.

This should be more efficient than iterating over all names in `ns` and calling `find`,
since it doesn't need to worry about overlapping prefixes.
-/
def findAny (r : NamePrefixRel) (n₁ : Name) (ns : Array Name) : Option (Name × Name) :=
  let prefixes := Lean.Name.collectPrefixes ns
  n₁.findPrefix fun n₁' => do
    let ns ← r.find? n₁'
    for n₂' in prefixes do
      if ns.contains n₂'
      then return (n₁', n₂')
      else pure ()
    none

/-- Is a prefix of `n₁` related to a prefix of `n₂`? -/
def contains (r : NamePrefixRel) (n₁ n₂ : Name) : Bool := (r.find n₁ n₂).isSome

end NamePrefixRel

/-- `forbiddenImportDirs` relates module prefixes, specifying that modules with the first prefix
should not import modules with the second prefix (except if specifically allowed in
`overrideAllowedImportDirs`).

For example, ``(`Mathlib.Algebra.Notation, `Mathlib.Algebra)`` is in `forbiddenImportDirs` and
``(`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation)`` is in `overrideAllowedImportDirs`
because modules in `Mathlib.Algebra.Notation` cannot import modules in `Mathlib.Algebra` that are
outside `Mathlib.Algebra.Notation`.
-/
def forbiddenImportDirs : NamePrefixRel := .ofArray #[
  (`Mathlib.Data, `Mathlib.Dynamics),
  (`Mathlib.Algebra.Notation, `Mathlib.Algebra),
  -- (`Mathlib.Topology, `Mathlib.Algebra),
]

/-- `overrideAllowedImportDirs` relates module prefixes, specifying that modules with the first
prefix are allowed to import modules with the second prefix, even if disallowed in
`forbiddenImportDirs`.

For example, ``(`Mathlib.Algebra.Notation, `Mathlib.Algebra)`` is in `forbiddenImportDirs` and
``(`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation)`` is in `overrideAllowedImportDirs`
because modules in `Mathlib.Algebra.Notation` cannot import modules in `Mathlib.Algebra` that are
outside `Mathlib.Algebra.Notation`.
-/
def overrideAllowedImportDirs : NamePrefixRel := .ofArray #[
  (`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation),
  (`Mathlib.Topology.Algebra, `Mathlib.Algebra),
]

end DirectoryDependency

open DirectoryDependency

@[inherit_doc Mathlib.Linter.linter.directoryDependency]
def directoryDependencyCheck (mainModule : Name) : CommandElabM (Option MessageData) := do
  unless Linter.getLinterValue linter.directoryDependency (← getOptions) do
    return none
  let env ← getEnv
  let imports := env.allImportedModuleNames
  match forbiddenImportDirs.findAny mainModule imports with
  | some (n₁, n₂) => do
    if let some imported := n₂.prefixToName imports then
      if !overrideAllowedImportDirs.contains mainModule imported then
        let mut msg := m!"Modules starting with {n₁} are not allowed to import modules starting with {n₂}.
This module depends on {imported}\n"
        for dep in env.importPath imported do
          msg := msg ++ m!"which is imported by {dep},\n"
        return some <| msg ++ m!"which is imported by this module.
(Exceptions can be added to `overrideAllowedImportDirs`.)"
    else
      return some m!"Internal error in `directoryDependency` linter: this module claims to depend on a module starting with {n₂} but a module with that prefix was not found in the import graph."
  | none => pure ()
  return none

end Mathlib.Linter
