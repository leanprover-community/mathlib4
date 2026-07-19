/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.ParseImportsFast
public meta import Lean.Linter.Basic
public meta import Lean.Elab.AssertExists
meta import Lean.Data.Json.FromToJson.Extra
public import Lean.Message

-- This file is imported by the Header linter, hence has no mathlib imports.

/-! # The `directoryDependency` linter

The `directoryDependency` linter detects imports between directories that are supposed to be
independent. By specifying that one directory does not import from another, we can improve the
modularity of Mathlib.
-/

meta section

-- XXX: is there a better long-time place for this?
/-- Parse all imports in a text file at `path` and return just their names:
this is just a thin wrapper around `Lean.parseImports'`.
Omit `Init` (which is part of the prelude). -/
public def findImports (path : System.FilePath) : IO (Array Lean.Name) := do
  return (← Lean.parseImports' (← IO.FS.readFile path) path.toString).imports
    |>.map (fun imp ↦ imp.module) |>.erase `Init

-- XXX: is there a better location for these?
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
  ns.foldl (fun ns n => ns.append n.prefixes) ∅

/-- Find a name in `ns` that starts with prefix `p`. -/
def Lean.Name.prefixToName (p : Name) (ns : Array Name) : Option Name :=
  ns.find? p.isPrefixOf

namespace Mathlib.Linter

open Lean Elab Command Linter

/--
The `directoryDependency` linter detects imports between directories that are supposed to be
independent. If this is the case, it emits a warning.
-/
public register_option linter.directoryDependency : Bool := {
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

-- The new behaviour of `inferInstanceAs` from leanprover/lean4#12897 needs to be updated,
-- to ensure that if we are in a `meta` section then the auxiliary definitions are also `meta`.
-- Fixed in https://github.com/leanprover/lean4/pull/13043
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
    let some rules := r.find? prefix_ | unreachable!
    allRules := allRules.append rules
  allRules

end NamePrefixRel

-- TODO: add/extend tests for this linter, to ensure the allow-list works
-- TODO: move the two remaining lists below to `scripts/forbiddenDirs.json` as well,
-- for easier evolution over time! Until then, beware that a rule change in the JSON file
-- may need a matching update to `overrideAllowedImportDirs` below (and vice versa).
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

  (`Mathlib.Lean, `Batteries.Tactic.Lint),
  (`Mathlib.Lean, `Batteries.CodeAction),
  -- TODO: should this be minimised further?
  (`Mathlib.Lean.Meta.CongrTheorems, `Batteries),
  -- These modules are transitively imported by `Batteries.CodeAction.
  (`Mathlib.Lean, `Batteries.Classes.SatisfiesM),
  (`Mathlib.Lean, `Batteries.Data.Array.Match),
  (`Mathlib.Lean, `Batteries.Data.Fin),
  (`Mathlib.Lean, `Batteries.Data.List),
  (`Mathlib.Lean, `Batteries.Lean),
  (`Mathlib.Lean, `Batteries.Control),
  (`Mathlib.Lean, `Batteries.Tactic.Alias),
  (`Mathlib.Lean, `Batteries.Util.ProofWanted),

  (`Mathlib.Lean.Expr, `Mathlib.Util),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Util),
  -- Fine-grained exceptions: TODO decide if these are fine, or should be scoped more broadly.
  (`Mathlib.Lean.CoreM, `Mathlib.Tactic.ToExpr),
  (`Mathlib.Lean.CoreM, `Mathlib.Util.WhatsNew),
  (`Mathlib.Lean.Meta.RefinedDiscrTree, `Mathlib.Tactic.Lemma),
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

  (`Mathlib.Lean.Expr.ExtraRecognizers, `Batteries.Util.ExtendedBinder),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Batteries.Logic),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Batteries.Tactic.Trans),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Batteries.Tactic.Init),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Data),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Order),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Logic),
  (`Mathlib.Lean.Expr.ExtraRecognizers, `Mathlib.Tactic),

  (`Mathlib.Tactic.Linter, `Batteries),
  -- The Mathlib.Tactic.Linter *module* imports all linters, hence requires all the imports.
  -- For more fine-grained exceptions of the next two imports, one needs to rename that file.
  (`Mathlib.Tactic.Linter, `ImportGraph),
  (`Mathlib.Tactic.Linter, `Mathlib.Tactic.MinImports),
  (`Mathlib.Tactic.Linter.OverlappingInstances, `Mathlib.Lean.ContextInfo),
  (`Mathlib.Tactic.Linter.OverlappingInstances, `Mathlib.Lean.Elab.Tactic.Meta),
  (`Mathlib.Tactic.Linter.TextBased, `Mathlib.Data.Nat.Notation),
  (`Mathlib.Tactic.Linter.UnusedInstancesInType, `Mathlib.Lean.Expr.Basic),
  (`Mathlib.Tactic.Linter.UnusedInstancesInType, `Mathlib.Lean.Environment),
  (`Mathlib.Tactic.Linter.UnusedInstancesInType, `Mathlib.Lean.Elab.InfoTree),

  (`Mathlib.Logic, `Batteries),
  -- TODO: should the next import direction be flipped?
  (`Mathlib.Logic, `Mathlib.Control),
  (`Mathlib.Logic, `Mathlib.Lean),
  (`Mathlib.Logic, `Mathlib.Util),
  (`Mathlib.Logic, `Mathlib.Tactic),
  (`Mathlib.Logic.Fin.Rotate, `Mathlib.Algebra.Group.Fin.Basic),
  (`Mathlib.Logic, `Mathlib.Algebra.Notation),
  (`Mathlib.Logic, `Mathlib.Algebra.NeZero),
  (`Mathlib.Logic, `Mathlib.Algebra.Order),
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

def extractNonComments (input : String) : String :=
  "\n".intercalate <| (input.splitOn "\n").filter fun l ↦ !l.trimAsciiStart.startsWith "//"

def readJsonFileWithComments (α) [FromJson α] (path : System.FilePath) : IO α := do
  let json ← IO.ofExcept <| Json.parse <| extractNonComments (← IO.FS.readFile path)
  IO.ofExcept <| fromJson? json

/-- The configuration file for `forbiddenImportDirs`, relative to the mathlib root directory. -/
def forbiddenDirsPath : System.FilePath := "scripts" / "forbiddenDirs.json"

/-- The root modules of the libraries built from the mathlib repository itself.
When elaborating one of their modules, the linter configuration file must be present. -/
def mathlibRoots : List Name := [`Mathlib, `MathlibTest, `Archive, `Counterexamples]

/-- Cache for `forbiddenImportDirs`: the configuration file is read at most once per process. -/
initialize forbiddenImportDirsCache : IO.Ref (Option NamePrefixRel) ← IO.mkRef none

/-- `forbiddenImportDirs` relates module prefixes, specifying that modules with the first prefix
should not import modules with the second prefix (except if specifically allowed in
`overrideAllowedImportDirs`).

For example, `scripts/forbiddenDirs.json` contains the entry
`"Mathlib.Algebra.Notation": ["Mathlib.Algebra"]` and ``(`Mathlib.Algebra.Notation,
`Mathlib.Algebra.Notation)`` is in `overrideAllowedImportDirs` because modules in
`Mathlib/Algebra/Notation.lean` cannot import modules in `Mathlib.Algebra` that are
outside `Mathlib/Algebra/Notation.lean`.

This relation is read at runtime from `scripts/forbiddenDirs.json`, so that updating the
configuration does not require recompiling this linter (and everything importing it).
-/
def forbiddenImportDirs : IO NamePrefixRel := do
  if let some rel := ← forbiddenImportDirsCache.get then
    return rel
  let entries ← readJsonFileWithComments (Std.TreeMap String (Array String)) forbiddenDirsPath
  let rel : NamePrefixRel := .ofArray <|
    entries.toArray.flatMap fun (n₁, ns) ↦ ns.map fun n₂ ↦ (n₁.toName, n₂.toName)
  forbiddenImportDirsCache.set (some rel)
  return rel

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
  (`Mathlib.Algebra.Module.ZLattice, `Mathlib.Analysis),
  (`Mathlib.Algebra.Notation, `Mathlib.Algebra.Notation),
  (`Mathlib.AlgebraicGeometry.EllipticCurve, `Mathlib.Probability), -- For L-functions
  (`Mathlib.AlgebraicGeometry.Sites, `Mathlib.AlgebraicTopology), -- Homotopical methods for sheaf cohomology
  (`Mathlib.AlgebraicGeometry.Sites, `Mathlib.NumberTheory), -- For arithmetic applications
  (`Mathlib.Deprecated, `Mathlib.Deprecated),
  (`Mathlib.LinearAlgebra.Complex, `Mathlib.Topology), -- Complex numbers are analysis/topology.
  (`Mathlib.LinearAlgebra.Matrix, `Mathlib.Topology), -- For e.g. spectra.
  (`Mathlib.LinearAlgebra.QuadraticForm, `Mathlib.Topology), -- For real/complex quadratic forms.
  (`Mathlib.LinearAlgebra.SesquilinearForm, `Mathlib.Topology), -- for links with positive semidefinite matrices
  (`Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap, `Mathlib.Topology),
  (`Mathlib.ModelTheory.Topology, `Mathlib.Topology), -- For e.g. topology on complete types.
  (`Mathlib.LinearAlgebra.RootSystem.IsValuedIn, `Mathlib.Topology),
  (`Mathlib.Topology.Algebra, `Mathlib.Algebra),
  (`Mathlib.Topology.Compactification, `Mathlib.Geometry.Manifold),
  (`Mathlib.Computability.AkraBazzi, `Mathlib.MeasureTheory), -- Akra-Bazzi uses calculus
  (`Mathlib.Analysis.Convex.SimplicialComplex.Basic, `Mathlib.AlgebraicTopology),
  (`Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion, `Mathlib.AlgebraicTopology),
  (`Mathlib.Probability.Kernel.Category, `Mathlib.CategoryTheory), -- For the category of s-finite/Markov kernels
  (`Mathlib.RepresentationTheory.Continuous, `Mathlib.Topology), -- For continuous representations
  (`Mathlib.RepresentationTheory.Homological.ContCohomology, `Mathlib.Topology),  -- For continuous cohomology
  -- TODO: think about the role of Analysis and Algebra, and perhaps further separation
  (`Mathlib.Algebra.Order.Archimedean.Real, `Mathlib.Analysis),
  (`Mathlib.Algebra.Star.CHSH, `Mathlib.Analysis),
  (`Mathlib.Algebra.Order.Star.Real, `Mathlib.Analysis),
  (`Mathlib.Topology.ContinuousMap.ContinuousSqrt, `Mathlib.Algebra.Order),
  (`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus, `Mathlib.Algebra.Order),
  (`Mathlib.Algebra.Order.Ring.StandardPart, `Mathlib.Analysis),
]

end DirectoryDependency

open DirectoryDependency

/-- Check if one of the imports `imports` to `mainModule` is forbidden by the relation
`forbidden` (see `forbiddenImportDirs`); if so, return an error describing how the import
transitively arises. -/
def checkBlocklist (env : Environment) (forbidden : NamePrefixRel) (mainModule : Name)
    (imports : Array Name) : Option MessageData := Id.run do
  match forbidden.findAny mainModule imports with
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
public def directoryDependencyCheck (mainModule : Name) : CommandElabM (Array MessageData) := do
  unless Linter.getLinterValue linter.directoryDependency (← Linter.getLinterOptions) do
    return #[]
  let env ← getEnv
  let imports := env.allImportedModuleNames

  -- If this module is in the allow-list, we only allow imports from directories specified there.
  -- Collect all prefixes which have a matching entry.
  let matchingPrefixes := mainModule.prefixes.filter (fun prf ↦ allowedImportDirs.containsKey prf)
  if matchingPrefixes.isEmpty then
    -- Otherwise, we fall back to the blocklist `forbiddenImportDirs`.
    unless ← forbiddenDirsPath.pathExists do
      -- When mathlib is used as a dependency, its configuration file is not available;
      -- in that case, there is nothing to check.
      -- Within mathlib itself, the file must exist: fail loudly if it does not.
      if mathlibRoots.contains mainModule.getRoot then
        throwError "directoryDependency linter: configuration file '{forbiddenDirsPath}' \
          not found; was mathlib built from its root directory?"
      return #[]
    if let some msg := checkBlocklist env (← forbiddenImportDirs) mainModule imports then
      return #[msg]
    else return #[]
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
