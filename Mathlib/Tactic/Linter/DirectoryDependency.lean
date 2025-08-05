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

-- XXX: is there a better long-time place for this
/-- Parse all imports in a text file at `path` and return just their names:
this is just a thin wrapper around `Lean.parseImports'`.
Omit `Init` (which is part of the prelude). -/
def findImports (path : System.FilePath) : IO (Array Lean.Name) := do
  return (← Lean.parseImports' (← IO.FS.readFile path) path.toString).imports
    |>.map (fun imp ↦ imp.module) |>.erase `Init

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

/-- Return the immediate prefix of `n` (if any). -/
def Lean.Name.prefix? (n : Name) : Option Name :=
  match n with
    | anonymous => none
    | str n' _ => some n'
    | num n' _ => some n'

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

open Lean Elab Command Linter

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

/-- Does `r` contain any entries with key `n`? -/
def containsKey (r : NamePrefixRel) (n : Name) : Bool := NameMap.contains r n

/-- Is a prefix of `n₁` related to a prefix of `n₂`? -/
def contains (r : NamePrefixRel) (n₁ n₂ : Name) : Bool := (r.find n₁ n₂).isSome

/-- Look up all names `m` which are values of some prefix of `n` under this relation. -/
def getAllLeft (r : NamePrefixRel) (n : Name) : NameSet := Id.run do
  let matchingPrefixes := n.prefixes.filter (fun prf ↦ r.containsKey prf)
  let mut allRules := NameSet.empty
  for prefix_ in matchingPrefixes do
    let some rules := RBMap.find? r prefix_ | unreachable!
    allRules := allRules.append rules
  allRules

end NamePrefixRel

-- TODO: add/extend tests for this linter, to ensure the allow-list works
-- TODO: move the following three lists to a JSON file, for easier evolution over time!
-- Future: enforce that allowed and forbidden keys are disjoint
-- Future: move further directories to use this allow-list instead of the blocklist

/-- `allowedImportDirs` relates module prefixes, specifying that modules with the first prefix
are only allowed to import modules in the second directory.
For directories which are low in the import hierarchy, this opt-out approach is both more ergonomic
(fewer updates needed) and needs less configuration.

We always allow imports of `Init`, `Lean`, `Std`, `Qq` and
`Mathlib.Init` (as well as their transitive dependencies.)
-/
def allowedImportDirs : NamePrefixRel := .ofArray #[
  -- This is used to test the linter.
  (`MathlibTest.DirectoryDependencyLinter, `Mathlib.Lean),
  -- Mathlib.Tactic has large transitive imports: just allow all of mathlib,
  -- as we don't care about the details a lot.
  (`MathlibTest.Header, `Mathlib),
  (`MathlibTest.Header, `Aesop),
  (`MathlibTest.Header, `ImportGraph),
  (`MathlibTest.Header, `LeanSearchClient),
  (`MathlibTest.Header, `Plausible),
  (`MathlibTest.Header, `ProofWidgets),
  (`MathlibTest.Header, `Qq),
  -- (`MathlibTest.Header, `Mathlib.Tactic),
  -- (`MathlibTest.Header, `Mathlib.Deprecated),
  (`MathlibTest.Header, `Batteries),
  (`MathlibTest.Header, `Lake),

  (`Mathlib.Util, `Batteries),
  (`Mathlib.Util, `Mathlib.Lean),
  (`Mathlib.Util, `Mathlib.Tactic),
  -- TODO: reduce this dependency by upstreaming `Data.String.Defs to batteries
  (`Mathlib.Util.FormatTable, `Mathlib.Data.String.Defs),

  (`Mathlib.Lean, `Batteries.CodeAction),
  (`Mathlib.Lean, `Batteries.Tactic.Lint),
  -- TODO: decide if this is acceptable or should be split in a more fine-grained way
  (`Mathlib.Lean, `Batteries),
  (`Mathlib.Lean.Expr, `Mathlib.Util),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Util),
  -- Fine-grained exceptions: TODO decide if these are fine, or should be scoped more broadly.
  (`Mathlib.Lean.CoreM, `Mathlib.Tactic.ToExpr),
  (`Mathlib.Lean.CoreM, `Mathlib.Util.WhatsNew),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic.Lemma),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic.TypeStar),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic.ToAdditive),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic), -- split this up further?
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Data), -- split this up further?
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Algebra.Notation),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Data.Notation),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Data.Array),

  (`Mathlib.Lean.Meta.CongrTheorems, `Mathlib.Data),
  (`Mathlib.Lean.Meta.CongrTheorems, `Mathlib.Logic),
  (`Mathlib.Lean.Meta.CongrTheorems, `Mathlib.Order.Defs),
  (`Mathlib.Lean.Meta.CongrTheorems, `Mathlib.Tactic),

  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Data),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Order),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Logic),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Tactic),

  (`Mathlib.Tactic.Linter, `Batteries),
  -- The Mathlib.Tactic.Linter *module* imports all linters, hence requires all the imports.
  -- For more fine-grained exceptions of the next two imports, one needs to rename that file.
  (`Mathlib.Tactic.Linter, `ImportGraph),
  (`Mathlib.Tactic.Linter, `Mathlib.Tactic.MinImports),
  (`Mathlib.Tactic.Linter.TextBased, `Mathlib.Data.Nat.Notation),

  (`Mathlib.Logic, `Batteries),
  -- TODO: should the next import direction be flipped?
  (`Mathlib.Logic, `Mathlib.Control),
  (`Mathlib.Logic, `Mathlib.Lean),
  (`Mathlib.Logic, `Mathlib.Util),
  (`Mathlib.Logic, `Mathlib.Tactic),
  (`Mathlib.Logic.Fin.Rotate, `Mathlib.Algebra.Group.Fin.Basic),
  (`Mathlib.Logic.Hydra, `Mathlib.GroupTheory),
  (`Mathlib.Logic, `Mathlib.Algebra.Notation),
  (`Mathlib.Logic, `Mathlib.Algebra.NeZero),
  (`Mathlib.Logic, `Mathlib.Data),
  -- TODO: this next dependency should be made more fine-grained.
  (`Mathlib.Logic, `Mathlib.Order),
  -- Particular modules with larger imports.
  (`Mathlib.Logic.Hydra, `Mathlib.GroupTheory),
  (`Mathlib.Logic.Hydra, `Mathlib.Algebra),
  (`Mathlib.Logic.Encodable.Pi, `Mathlib.Algebra),
  (`Mathlib.Logic.Equiv.Fin.Rotate, `Mathlib.Algebra.Group),
  (`Mathlib.Logic.Equiv.Fin.Rotate, `Mathlib.Algebra.Regular),
  (`Mathlib.Logic.Equiv.Array, `Mathlib.Algebra),
  (`Mathlib.Logic.Equiv.Finset, `Mathlib.Algebra),
  (`Mathlib.Logic.Godel.GodelBetaFunction, `Mathlib.Algebra),
  (`Mathlib.Logic.Small.List, `Mathlib.Algebra),

  (`Mathlib.Testing, `Batteries),
  -- TODO: this next import should be eliminated.
  (`Mathlib.Testing, `Mathlib.GroupTheory),
  (`Mathlib.Testing, `Mathlib.Control),
  (`Mathlib.Testing, `Mathlib.Algebra),
  (`Mathlib.Testing, `Mathlib.Data),
  (`Mathlib.Testing, `Mathlib.Logic),
  (`Mathlib.Testing, `Mathlib.Order),
  (`Mathlib.Testing, `Mathlib.Lean),
  (`Mathlib.Testing, `Mathlib.Tactic),
  (`Mathlib.Testing, `Mathlib.Util),
]

/-- `forbiddenImportDirs` relates module prefixes, specifying that modules with the first prefix
should not import modules with the second prefix (except if specifically allowed in
`overrideAllowedImportDirs`).

For example, ``(`Mathlib.Algebra.Notation, `Mathlib.Algebra)`` is in `forbiddenImportDirs` and
``(`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation)`` is in `overrideAllowedImportDirs`
because modules in `Mathlib/Algebra/Notation.lean` cannot import modules in `Mathlib.Algebra` that are
outside `Mathlib/Algebra/Notation.lean`.
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
  (`Mathlib.Combinatorics, `Mathlib.Geometry.Euclidean),
  (`Mathlib.Combinatorics, `Mathlib.Geometry.Group),
  (`Mathlib.Combinatorics, `Mathlib.Geometry.Manifold),
  (`Mathlib.Combinatorics, `Mathlib.Geometry.RingedSpace),
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
  (`Mathlib.Data, `Mathlib.Geometry.Euclidean),
  (`Mathlib.Data, `Mathlib.Geometry.Group),
  (`Mathlib.Data, `Mathlib.Geometry.Manifold),
  (`Mathlib.Data, `Mathlib.Geometry.RingedSpace),
  (`Mathlib.Data, `Mathlib.InformationTheory),
  (`Mathlib.Data, `Mathlib.ModelTheory),
  (`Mathlib.Data, `Mathlib.RepresentationTheory),
  (`Mathlib.Data, `Mathlib.Testing),
  (`Mathlib.Dynamics, `Mathlib.AlgebraicGeometry),
  (`Mathlib.Dynamics, `Mathlib.AlgebraicTopology),
  (`Mathlib.Dynamics, `Mathlib.CategoryTheory),
  (`Mathlib.Dynamics, `Mathlib.Computability),
  (`Mathlib.Dynamics, `Mathlib.Condensed),
  (`Mathlib.Dynamics, `Mathlib.Geometry.Euclidean),
  (`Mathlib.Dynamics, `Mathlib.Geometry.Group),
  (`Mathlib.Dynamics, `Mathlib.Geometry.Manifold),
  (`Mathlib.Dynamics, `Mathlib.Geometry.RingedSpace),
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
  (`Mathlib.InformationTheory, `Mathlib.Geometry.Euclidean),
  (`Mathlib.InformationTheory, `Mathlib.Geometry.Group),
  (`Mathlib.InformationTheory, `Mathlib.Geometry.Manifold),
  (`Mathlib.InformationTheory, `Mathlib.Geometry.RingedSpace),
  (`Mathlib.InformationTheory, `Mathlib.ModelTheory),
  (`Mathlib.InformationTheory, `Mathlib.RepresentationTheory),
  (`Mathlib.InformationTheory, `Mathlib.Testing),
  (`Mathlib.LinearAlgebra, `Mathlib.AlgebraicGeometry),
  (`Mathlib.LinearAlgebra, `Mathlib.AlgebraicTopology),
  (`Mathlib.LinearAlgebra, `Mathlib.Computability),
  (`Mathlib.LinearAlgebra, `Mathlib.Condensed),
  (`Mathlib.LinearAlgebra, `Mathlib.Geometry.Euclidean),
  (`Mathlib.LinearAlgebra, `Mathlib.Geometry.Group),
  (`Mathlib.LinearAlgebra, `Mathlib.Geometry.Manifold),
  (`Mathlib.LinearAlgebra, `Mathlib.Geometry.RingedSpace),
  (`Mathlib.LinearAlgebra, `Mathlib.InformationTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.MeasureTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.ModelTheory),
  (`Mathlib.LinearAlgebra, `Mathlib.Probability),
  (`Mathlib.LinearAlgebra, `Mathlib.Testing),
  (`Mathlib.MeasureTheory, `Mathlib.AlgebraicGeometry),
  (`Mathlib.MeasureTheory, `Mathlib.AlgebraicTopology),
  (`Mathlib.MeasureTheory, `Mathlib.Computability),
  (`Mathlib.MeasureTheory, `Mathlib.Condensed),
  (`Mathlib.MeasureTheory, `Mathlib.Geometry.Euclidean),
  (`Mathlib.MeasureTheory, `Mathlib.Geometry.Group),
  (`Mathlib.MeasureTheory, `Mathlib.Geometry.Manifold),
  (`Mathlib.MeasureTheory, `Mathlib.Geometry.RingedSpace),
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
  (`Mathlib.Probability, `Mathlib.Geometry.Euclidean),
  (`Mathlib.Probability, `Mathlib.Geometry.Group),
  (`Mathlib.Probability, `Mathlib.Geometry.Manifold),
  (`Mathlib.Probability, `Mathlib.Geometry.RingedSpace),
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
  (`Mathlib.RingTheory, `Mathlib.Geometry.Euclidean),
  (`Mathlib.RingTheory, `Mathlib.Geometry.Group),
  (`Mathlib.RingTheory, `Mathlib.Geometry.Manifold),
  (`Mathlib.RingTheory, `Mathlib.Geometry.RingedSpace),
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
because modules in `Mathlib/Algebra/Notation.lean` cannot import modules in `Mathlib.Algebra` that are
outside `Mathlib/Algebra/Notation.lean`.
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

/-- Check if one of the imports `imports` to `mainModule` is forbidden by `forbiddenImportDirs`;
if so, return an error describing how the import transitively arises. -/
private def checkBlocklist (env : Environment) (mainModule : Name) (imports : Array Name) : Option MessageData := Id.run do
  match forbiddenImportDirs.findAny mainModule imports with
  | some (n₁, n₂) => do
    if let some imported := n₂.prefixToName imports then
      if !overrideAllowedImportDirs.contains mainModule imported then
        let mut msg := m!"Modules starting with {n₁} are not allowed to import modules starting with {n₂}. \
        This module depends on {imported}\n"
        for dep in env.importPath imported do
          msg := msg ++ m!"which is imported by {dep},\n"
        return some (msg ++ m!"which is imported by this module. \
          (Exceptions can be added to `overrideAllowedImportDirs`.)")
      else none
    else
      return some m!"Internal error in `directoryDependency` linter: this module claims to depend \
      on a module starting with {n₂} but a module with that prefix was not found in the import graph."
  | none => none

@[inherit_doc Mathlib.Linter.linter.directoryDependency]
def directoryDependencyCheck (mainModule : Name) : CommandElabM (Array MessageData) := do
  unless Linter.getLinterValue linter.directoryDependency (← getLinterOptions) do
    return #[]
  let env ← getEnv
  let imports := env.allImportedModuleNames

  -- If this module is in the allow-list, we only allow imports from directories specified there.
  -- Collect all prefixes which have a matching entry.
  let matchingPrefixes := mainModule.prefixes.filter (fun prf ↦ allowedImportDirs.containsKey prf)
  if matchingPrefixes.isEmpty then
    -- Otherwise, we fall back to the blocklist `forbiddenImportDirs`.
    if let some msg := checkBlocklist env mainModule imports then return #[msg] else return #[]
  else
    -- We always allow imports in the same directory (for each matching prefix),
    -- from `Init`, `Lean` and `Std`, as well as imports in `Aesop`, `Qq`, `Plausible`,
    -- `ImportGraph`, `ProofWidgets` or `LeanSearchClient` (as these are imported in Tactic.Common).
    -- We also allow transitive imports of Mathlib.Init, as well as Mathlib.Init itself.
    let initImports := (← findImports ("Mathlib" / "Init.lean")).append
      #[`Mathlib.Init, `Mathlib.Tactic.DeclarationNames]
    let exclude := [
      `Init, `Std, `Lean,
      `Aesop, `Qq, `Plausible, `ImportGraph, `ProofWidgets, `LeanSearchClient
    ]
    let importsToCheck := imports.filter (fun imp ↦ !exclude.any (·.isPrefixOf imp))
      |>.filter (fun imp ↦ !matchingPrefixes.any (·.isPrefixOf imp))
      |>.filter (!initImports.contains ·)

    -- Find all prefixes which are allowed for one of these directories.
    let allRules := allowedImportDirs.getAllLeft mainModule
    -- Error about those imports which are not covered by allowedImportDirs.
    let mut messages := #[]
    for imported in importsToCheck do
      if !allowedImportDirs.contains mainModule imported then
        let importPath := env.importPath imported
        let mut msg := m!"Module {mainModule} depends on {imported},\n\
        but is only allowed to import modules starting with one of \
        {allRules.toArray.qsort (·.toString < ·.toString)}.\n\
        Note: module {imported}"
        let mut superseded := false
        match importPath.toList with
        | [] => msg := msg ++ " is directly imported by this module"
        | a :: rest =>
          -- Only add messages about imports that aren't themselves transitive imports of
          -- forbidden imports.
          -- This should prevent redundant messages.
          if !allowedImportDirs.contains mainModule a then
            superseded := true
          else
            msg := msg ++ s!" is imported by {a},\n"
            for dep in rest do
              if !allowedImportDirs.contains mainModule dep then
                superseded := true
                break
              msg := msg ++ m!"which is imported by {dep},\n"
            msg := msg ++ m!"which is imported by this module."
            msg := msg ++ "(Exceptions can be added to `allowedImportDirs`.)"
        if !superseded then
          messages := messages.push msg
    return messages

end Mathlib.Linter
