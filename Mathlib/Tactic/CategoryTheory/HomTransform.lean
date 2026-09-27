/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Util.TheoremTransform
public import Qq

/-!
# Shared operations for transformations of categorical equalities

This layer recognizes morphism equalities by definitional equality, including inherited, opposite,
and functor-category instances. Category matching and universe classification belong here rather
than in the category-independent theorem transformation engine.
-/

public meta section

open Lean Meta Elab Term Qq CategoryTheory
open Mathlib.Tactic.TheoremTransform

namespace Mathlib.Tactic.CategoryTheory

/-- The data of an equality of morphisms, as recognized by `matchHomEquality`.
`inst` is a synthetic instance metavariable, possibly already assigned. -/
structure HomEquality where
  /-- Universe of objects. -/
  u : Level
  /-- Universe of morphisms. -/
  v : Level
  /-- Type of objects of the source category. -/
  C : Q(Type u)
  /-- Synthetic source instance, which may already have been assigned. -/
  inst : Q(Category.{v} $C)
  /-- Common domain of the two morphisms. -/
  X : Q($C)
  /-- Common codomain of the two morphisms. -/
  Y : Q($C)
  /-- Left-hand side of the equality. -/
  f : Q($X ⟶ $Y)
  /-- Right-hand side of the equality. -/
  g : Q($X ⟶ $Y)

/-- Recognize an equality of morphisms without requiring a syntactic category projection chain.
The surrounding transformation driver restores state when recognition fails. -/
def matchHomEquality (p : Proof) (attrName : Name) :
    TermElabM (Except MessageData HomEquality) := do
  let some _ := p.type.eq? | return .error m!"`@[{attrName}]` expects an equality"
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let C ← mkFreshExprMVarQ q(Type u)
  let instC ← mkFreshExprMVarQ q(Category.{v} $C) .synthetic
  let X ← mkFreshExprMVarQ q($C)
  let Y ← mkFreshExprMVarQ q($C)
  let f ← mkFreshExprMVarQ q($X ⟶ $Y)
  let g ← mkFreshExprMVarQ q($X ⟶ $Y)
  unless ← isDefEq p.type q($f = $g) do
    return .error m!"`@[{attrName}]` expects an equality of morphisms"
  return .ok ⟨u, v, C, instC, X, Y, f, g⟩

/-- Normalize with the source category instance available, allowing deferred term inference. -/
def normalizeHomProof (inst : Expr) (p : Proof) (simp : Expr → MetaM Simp.Result) :
    TermElabM Proof := normalizeWithInstances p #[inst.mvarId!] (·.simpEq simp)

end Mathlib.Tactic.CategoryTheory
