/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Lean.Elab.Command

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
current module.

The path only contains the intermediate steps: it excludes `imported` and the current module.
-/
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
      if ns.contains n₂' then
        (n₁', n₂')
      else
        none

/-- Get a prefix of `n₁` that is related to any prefix of the names in `ns`; return the prefixes.

This should be more efficient than iterating over all names in `ns` and calling `find`,
since it doesn't need to worry about overlapping prefixes.
-/
def findAny (r : NamePrefixRel) (n₁ : Name) (ns : Array Name) : Option (Name × Name) :=
  let prefixes := Lean.Name.collectPrefixes ns
  n₁.findPrefix fun n₁' => do
    let ns ← r.find? n₁'
    for n₂' in prefixes do
      if ns.contains n₂' then
        return (n₁', n₂')
      else
        pure ()
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
  (`Mathlib.Algebra.Notation, `Mathlib.Algebra),
  (`Mathlib, `Mathlib.Deprecated),

  -- This is used to test the linter.
  (`MathlibTest.Header, `Mathlib.Deprecated),

  -- TODO:
  -- (`Mathlib.Data, `Mathlib.Dynamics),
  -- (`Mathlib.Topology, `Mathlib.Algebra),

  -- The following are a list of existing non-dependent top-level directory pairs.
  (`Mathlib.Algebra, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Algebra, `Mathlib.Computability),
  (`Mathlib.Algebra, `Mathlib.Condensed),
  (`Mathlib.Algebra, `Mathlib.Geometry),
  (`Mathlib.Algebra, `Mathlib.InformationTheory),
  (`Mathlib.Algebra, `Mathlib.ModelTheory),
  (`Mathlib.Algebra, `Mathlib.RepresentationTheory),
  (`Mathlib.Algebra, `Mathlib.Testing),
  (`Mathlib.AlgebraicGeometry, `Mathlib.AlgebraicTopology),
  (`Mathlib.AlgebraicGeometry, `Mathlib.Analysis),
  (`Mathlib.AlgebraicGeometry, `Mathlib.Computability),
  (`Mathlib.AlgebraicGeometry, `Mathlib.Condensed),
  (`Mathlib.AlgebraicGeometry, `Mathlib.InformationTheory),
  (`Mathlib.AlgebraicGeometry, `Mathlib.MeasureTheory),
  (`Mathlib.AlgebraicGeometry, `Mathlib.ModelTheory),
  (`Mathlib.AlgebraicGeometry, `Mathlib.Probability),
  (`Mathlib.AlgebraicGeometry, `Mathlib.RepresentationTheory),
  (`Mathlib.AlgebraicGeometry, `Mathlib.Testing),
  (`Mathlib.AlgebraicTopology, `Mathlib.AlgebraicGeometry),
  (`Mathlib.AlgebraicTopology, `Mathlib.Computability),
  (`Mathlib.AlgebraicTopology, `Mathlib.Condensed),
  (`Mathlib.AlgebraicTopology, `Mathlib.FieldTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.Geometry),
  (`Mathlib.AlgebraicTopology, `Mathlib.InformationTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.MeasureTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.ModelTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.NumberTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.Probability),
  (`Mathlib.AlgebraicTopology, `Mathlib.RepresentationTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.SetTheory),
  (`Mathlib.AlgebraicTopology, `Mathlib.Testing),
  (`Mathlib.Analysis, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Analysis, `Mathlib.AlgebraicTopology),
  (`Mathlib.Analysis, `Mathlib.Computability),
  (`Mathlib.Analysis, `Mathlib.Condensed),
  (`Mathlib.Analysis, `Mathlib.InformationTheory),
  (`Mathlib.Analysis, `Mathlib.ModelTheory),
  (`Mathlib.Analysis, `Mathlib.RepresentationTheory),
  (`Mathlib.Analysis, `Mathlib.Testing),
  (`Mathlib.CategoryTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.CategoryTheory, `Mathlib.Analysis),
  (`Mathlib.CategoryTheory, `Mathlib.Computability),
  (`Mathlib.CategoryTheory, `Mathlib.Condensed),
  (`Mathlib.CategoryTheory, `Mathlib.Geometry),
  (`Mathlib.CategoryTheory, `Mathlib.InformationTheory),
  (`Mathlib.CategoryTheory, `Mathlib.MeasureTheory),
  (`Mathlib.CategoryTheory, `Mathlib.ModelTheory),
  (`Mathlib.CategoryTheory, `Mathlib.Probability),
  (`Mathlib.CategoryTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.CategoryTheory, `Mathlib.Testing),
  (`Mathlib.Combinatorics, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Combinatorics, `Mathlib.AlgebraicTopology),
  (`Mathlib.Combinatorics, `Mathlib.Computability),
  (`Mathlib.Combinatorics, `Mathlib.Condensed),
  (`Mathlib.Combinatorics, `Mathlib.Geometry),
  (`Mathlib.Combinatorics, `Mathlib.InformationTheory),
  (`Mathlib.Combinatorics, `Mathlib.MeasureTheory),
  (`Mathlib.Combinatorics, `Mathlib.ModelTheory),
  (`Mathlib.Combinatorics, `Mathlib.Probability),
  (`Mathlib.Combinatorics, `Mathlib.RepresentationTheory),
  (`Mathlib.Combinatorics, `Mathlib.Testing),
  (`Mathlib.Computability, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Computability, `Mathlib.AlgebraicTopology),
  (`Mathlib.Computability, `Mathlib.CategoryTheory),
  (`Mathlib.Computability, `Mathlib.Condensed),
  (`Mathlib.Computability, `Mathlib.FieldTheory),
  (`Mathlib.Computability, `Mathlib.Geometry),
  (`Mathlib.Computability, `Mathlib.InformationTheory),
  (`Mathlib.Computability, `Mathlib.MeasureTheory),
  (`Mathlib.Computability, `Mathlib.ModelTheory),
  (`Mathlib.Computability, `Mathlib.Probability),
  (`Mathlib.Computability, `Mathlib.RepresentationTheory),
  (`Mathlib.Computability, `Mathlib.Testing),
  (`Mathlib.Condensed, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Condensed, `Mathlib.AlgebraicTopology),
  (`Mathlib.Condensed, `Mathlib.Computability),
  (`Mathlib.Condensed, `Mathlib.FieldTheory),
  (`Mathlib.Condensed, `Mathlib.Geometry),
  (`Mathlib.Condensed, `Mathlib.InformationTheory),
  (`Mathlib.Condensed, `Mathlib.MeasureTheory),
  (`Mathlib.Condensed, `Mathlib.ModelTheory),
  (`Mathlib.Condensed, `Mathlib.Probability),
  (`Mathlib.Condensed, `Mathlib.RepresentationTheory),
  (`Mathlib.Condensed, `Mathlib.Testing),
  (`Mathlib.Control, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Control, `Mathlib.AlgebraicTopology),
  (`Mathlib.Control, `Mathlib.Analysis),
  (`Mathlib.Control, `Mathlib.Computability),
  (`Mathlib.Control, `Mathlib.Condensed),
  (`Mathlib.Control, `Mathlib.FieldTheory),
  (`Mathlib.Control, `Mathlib.Geometry),
  (`Mathlib.Control, `Mathlib.GroupTheory),
  (`Mathlib.Control, `Mathlib.InformationTheory),
  (`Mathlib.Control, `Mathlib.LinearAlgebra),
  (`Mathlib.Control, `Mathlib.MeasureTheory),
  (`Mathlib.Control, `Mathlib.ModelTheory),
  (`Mathlib.Control, `Mathlib.NumberTheory),
  (`Mathlib.Control, `Mathlib.Probability),
  (`Mathlib.Control, `Mathlib.RepresentationTheory),
  (`Mathlib.Control, `Mathlib.RingTheory),
  (`Mathlib.Control, `Mathlib.SetTheory),
  (`Mathlib.Control, `Mathlib.Testing),
  (`Mathlib.Control, `Mathlib.Topology),
  (`Mathlib.Data, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Data, `Mathlib.AlgebraicTopology),
  (`Mathlib.Data, `Mathlib.Computability),
  (`Mathlib.Data, `Mathlib.Condensed),
  (`Mathlib.Data, `Mathlib.Geometry),
  (`Mathlib.Data, `Mathlib.InformationTheory),
  (`Mathlib.Data, `Mathlib.ModelTheory),
  (`Mathlib.Data, `Mathlib.RepresentationTheory),
  (`Mathlib.Data, `Mathlib.Testing),
  (`Mathlib.Dynamics, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Dynamics, `Mathlib.AlgebraicTopology),
  (`Mathlib.Dynamics, `Mathlib.CategoryTheory),
  (`Mathlib.Dynamics, `Mathlib.Computability),
  (`Mathlib.Dynamics, `Mathlib.Condensed),
  (`Mathlib.Dynamics, `Mathlib.Geometry),
  (`Mathlib.Dynamics, `Mathlib.InformationTheory),
  (`Mathlib.Dynamics, `Mathlib.ModelTheory),
  (`Mathlib.Dynamics, `Mathlib.RepresentationTheory),
  (`Mathlib.Dynamics, `Mathlib.Testing),
  (`Mathlib.FieldTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.FieldTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.FieldTheory, `Mathlib.Condensed),
  (`Mathlib.FieldTheory, `Mathlib.Geometry),
  (`Mathlib.FieldTheory, `Mathlib.InformationTheory),
  (`Mathlib.FieldTheory, `Mathlib.MeasureTheory),
  (`Mathlib.FieldTheory, `Mathlib.Probability),
  (`Mathlib.FieldTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.FieldTheory, `Mathlib.Testing),
  (`Mathlib.Geometry, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Geometry, `Mathlib.Computability),
  (`Mathlib.Geometry, `Mathlib.Condensed),
  (`Mathlib.Geometry, `Mathlib.InformationTheory),
  (`Mathlib.Geometry, `Mathlib.ModelTheory),
  (`Mathlib.Geometry, `Mathlib.RepresentationTheory),
  (`Mathlib.Geometry, `Mathlib.Testing),
  (`Mathlib.GroupTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.GroupTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.GroupTheory, `Mathlib.Analysis),
  (`Mathlib.GroupTheory, `Mathlib.Computability),
  (`Mathlib.GroupTheory, `Mathlib.Condensed),
  (`Mathlib.GroupTheory, `Mathlib.Geometry),
  (`Mathlib.GroupTheory, `Mathlib.InformationTheory),
  (`Mathlib.GroupTheory, `Mathlib.MeasureTheory),
  (`Mathlib.GroupTheory, `Mathlib.ModelTheory),
  (`Mathlib.GroupTheory, `Mathlib.Probability),
  (`Mathlib.GroupTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.GroupTheory, `Mathlib.Testing),
  (`Mathlib.GroupTheory, `Mathlib.Topology),
  (`Mathlib.InformationTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.InformationTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.InformationTheory, `Mathlib.CategoryTheory),
  (`Mathlib.InformationTheory, `Mathlib.Computability),
  (`Mathlib.InformationTheory, `Mathlib.Condensed),
  (`Mathlib.InformationTheory, `Mathlib.Geometry),
  (`Mathlib.InformationTheory, `Mathlib.ModelTheory),
  (`Mathlib.InformationTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.InformationTheory, `Mathlib.Testing),
  (`Mathlib.LinearAlgebra, `Mathlib.AlgebraicGeometry),
  (`Mathlib.LinearAlgebra, `Mathlib.AlgebraicTopology),
  (`Mathlib.LinearAlgebra, `Mathlib.Computability),
  (`Mathlib.LinearAlgebra, `Mathlib.Condensed),
  (`Mathlib.LinearAlgebra, `Mathlib.Geometry),
  (`Mathlib.LinearAlgebra, `Mathlib.InformationTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.MeasureTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.ModelTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.Probability),
  (`Mathlib.LinearAlgebra, `Mathlib.Testing),
  (`Mathlib.Logic, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Logic, `Mathlib.AlgebraicTopology),
  (`Mathlib.Logic, `Mathlib.Analysis),
  (`Mathlib.Logic, `Mathlib.CategoryTheory),
  (`Mathlib.Logic, `Mathlib.Combinatorics),
  (`Mathlib.Logic, `Mathlib.Computability),
  (`Mathlib.Logic, `Mathlib.Condensed),
  (`Mathlib.Logic, `Mathlib.Dynamics),
  (`Mathlib.Logic, `Mathlib.FieldTheory),
  (`Mathlib.Logic, `Mathlib.Geometry),
  (`Mathlib.Logic, `Mathlib.InformationTheory),
  (`Mathlib.Logic, `Mathlib.LinearAlgebra),
  (`Mathlib.Logic, `Mathlib.MeasureTheory),
  (`Mathlib.Logic, `Mathlib.ModelTheory),
  (`Mathlib.Logic, `Mathlib.NumberTheory),
  (`Mathlib.Logic, `Mathlib.Probability),
  (`Mathlib.Logic, `Mathlib.RepresentationTheory),
  (`Mathlib.Logic, `Mathlib.RingTheory),
  (`Mathlib.Logic, `Mathlib.SetTheory),
  (`Mathlib.Logic, `Mathlib.Testing),
  (`Mathlib.Logic, `Mathlib.Topology),
  (`Mathlib.MeasureTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.MeasureTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.MeasureTheory, `Mathlib.Computability),
  (`Mathlib.MeasureTheory, `Mathlib.Condensed),
  (`Mathlib.MeasureTheory, `Mathlib.Geometry),
  (`Mathlib.MeasureTheory, `Mathlib.InformationTheory),
  (`Mathlib.MeasureTheory, `Mathlib.ModelTheory),
  (`Mathlib.MeasureTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.MeasureTheory, `Mathlib.Testing),
  (`Mathlib.ModelTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.ModelTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.ModelTheory, `Mathlib.Analysis),
  (`Mathlib.ModelTheory, `Mathlib.Condensed),
  (`Mathlib.ModelTheory, `Mathlib.Geometry),
  (`Mathlib.ModelTheory, `Mathlib.InformationTheory),
  (`Mathlib.ModelTheory, `Mathlib.MeasureTheory),
  (`Mathlib.ModelTheory, `Mathlib.Probability),
  (`Mathlib.ModelTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.ModelTheory, `Mathlib.Testing),
  (`Mathlib.ModelTheory, `Mathlib.Topology),
  (`Mathlib.NumberTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.NumberTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.NumberTheory, `Mathlib.Computability),
  (`Mathlib.NumberTheory, `Mathlib.Condensed),
  (`Mathlib.NumberTheory, `Mathlib.InformationTheory),
  (`Mathlib.NumberTheory, `Mathlib.ModelTheory),
  (`Mathlib.NumberTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.NumberTheory, `Mathlib.Testing),
  (`Mathlib.Order, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Order, `Mathlib.AlgebraicTopology),
  (`Mathlib.Order, `Mathlib.Computability),
  (`Mathlib.Order, `Mathlib.Condensed),
  (`Mathlib.Order, `Mathlib.FieldTheory),
  (`Mathlib.Order, `Mathlib.Geometry),
  (`Mathlib.Order, `Mathlib.InformationTheory),
  (`Mathlib.Order, `Mathlib.MeasureTheory),
  (`Mathlib.Order, `Mathlib.ModelTheory),
  (`Mathlib.Order, `Mathlib.NumberTheory),
  (`Mathlib.Order, `Mathlib.Probability),
  (`Mathlib.Order, `Mathlib.RepresentationTheory),
  (`Mathlib.Order, `Mathlib.Testing),
  (`Mathlib.Probability, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Probability, `Mathlib.AlgebraicTopology),
  (`Mathlib.Probability, `Mathlib.CategoryTheory),
  (`Mathlib.Probability, `Mathlib.Computability),
  (`Mathlib.Probability, `Mathlib.Condensed),
  (`Mathlib.Probability, `Mathlib.Geometry),
  (`Mathlib.Probability, `Mathlib.InformationTheory),
  (`Mathlib.Probability, `Mathlib.ModelTheory),
  (`Mathlib.Probability, `Mathlib.RepresentationTheory),
  (`Mathlib.Probability, `Mathlib.Testing),
  (`Mathlib.RepresentationTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.RepresentationTheory, `Mathlib.Analysis),
  (`Mathlib.RepresentationTheory, `Mathlib.Computability),
  (`Mathlib.RepresentationTheory, `Mathlib.Condensed),
  (`Mathlib.RepresentationTheory, `Mathlib.Geometry),
  (`Mathlib.RepresentationTheory, `Mathlib.InformationTheory),
  (`Mathlib.RepresentationTheory, `Mathlib.MeasureTheory),
  (`Mathlib.RepresentationTheory, `Mathlib.ModelTheory),
  (`Mathlib.RepresentationTheory, `Mathlib.Probability),
  (`Mathlib.RepresentationTheory, `Mathlib.Testing),
  (`Mathlib.RepresentationTheory, `Mathlib.Topology),
  (`Mathlib.RingTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.RingTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.RingTheory, `Mathlib.Computability),
  (`Mathlib.RingTheory, `Mathlib.Condensed),
  (`Mathlib.RingTheory, `Mathlib.Geometry),
  (`Mathlib.RingTheory, `Mathlib.InformationTheory),
  (`Mathlib.RingTheory, `Mathlib.ModelTheory),
  (`Mathlib.RingTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.RingTheory, `Mathlib.Testing),
  (`Mathlib.SetTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.SetTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.SetTheory, `Mathlib.Analysis),
  (`Mathlib.SetTheory, `Mathlib.CategoryTheory),
  (`Mathlib.SetTheory, `Mathlib.Combinatorics),
  (`Mathlib.SetTheory, `Mathlib.Computability),
  (`Mathlib.SetTheory, `Mathlib.Condensed),
  (`Mathlib.SetTheory, `Mathlib.FieldTheory),
  (`Mathlib.SetTheory, `Mathlib.Geometry),
  (`Mathlib.SetTheory, `Mathlib.InformationTheory),
  (`Mathlib.SetTheory, `Mathlib.MeasureTheory),
  (`Mathlib.SetTheory, `Mathlib.ModelTheory),
  (`Mathlib.SetTheory, `Mathlib.Probability),
  (`Mathlib.SetTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.SetTheory, `Mathlib.Testing),
  (`Mathlib.Testing, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Testing, `Mathlib.AlgebraicTopology),
  (`Mathlib.Testing, `Mathlib.Analysis),
  (`Mathlib.Testing, `Mathlib.CategoryTheory),
  (`Mathlib.Testing, `Mathlib.Combinatorics),
  (`Mathlib.Testing, `Mathlib.Computability),
  (`Mathlib.Testing, `Mathlib.Condensed),
  (`Mathlib.Testing, `Mathlib.Dynamics),
  (`Mathlib.Testing, `Mathlib.FieldTheory),
  (`Mathlib.Testing, `Mathlib.Geometry),
  (`Mathlib.Testing, `Mathlib.InformationTheory),
  (`Mathlib.Testing, `Mathlib.LinearAlgebra),
  (`Mathlib.Testing, `Mathlib.MeasureTheory),
  (`Mathlib.Testing, `Mathlib.ModelTheory),
  (`Mathlib.Testing, `Mathlib.NumberTheory),
  (`Mathlib.Testing, `Mathlib.Probability),
  (`Mathlib.Testing, `Mathlib.RepresentationTheory),
  (`Mathlib.Testing, `Mathlib.RingTheory),
  (`Mathlib.Testing, `Mathlib.SetTheory),
  (`Mathlib.Testing, `Mathlib.Testing),
  (`Mathlib.Testing, `Mathlib.Topology),
  (`Mathlib.Topology, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Topology, `Mathlib.Computability),
  (`Mathlib.Topology, `Mathlib.Condensed),
  (`Mathlib.Topology, `Mathlib.Geometry),
  (`Mathlib.Topology, `Mathlib.InformationTheory),
  (`Mathlib.Topology, `Mathlib.ModelTheory),
  (`Mathlib.Topology, `Mathlib.Probability),
  (`Mathlib.Topology, `Mathlib.RepresentationTheory),
  (`Mathlib.Topology, `Mathlib.Testing),
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
  (`Mathlib.Algebra.Lie, `Mathlib.RepresentationTheory),
  (`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation),
  (`Mathlib.Deprecated, `Mathlib.Deprecated),
  (`Mathlib.Topology.Algebra, `Mathlib.Algebra),
  (`Mathlib.Topology.Compactification, `Mathlib.Geometry.Manifold)
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
