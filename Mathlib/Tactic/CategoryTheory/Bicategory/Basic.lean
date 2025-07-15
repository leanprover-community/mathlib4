/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence.Basic
import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence

/-!
# `bicategory` tactic

This file provides `bicategory` tactic, which solves equations in a bicategory, where
the two sides only differ by replacing strings of bicategory structural morphisms (that is,
associators, unitors, and identities) with different strings of structural morphisms with the same
source and target. In other words, `bicategory` solves equalities where both sides have the same
string diagrams.

The core function for the `bicategory` tactic is provided in
`Mathlib/Tactic/CategoryTheory/Coherence/Basic.lean`. See this file for more details about the
implementation.

-/

open Lean Meta Elab Tactic
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Mathlib.Tactic.Bicategory

/-- Normalize the both sides of an equality. -/
def bicategoryNf (mvarId : MVarId) : MetaM (List MVarId) := do
  BicategoryLike.normalForm Bicategory.Context `bicategory mvarId

@[inherit_doc bicategoryNf]
elab "bicategory_nf" : tactic => withMainContext do
  replaceMainGoal (← bicategoryNf (← getMainGoal))

/--
Use the coherence theorem for bicategories to solve equations in a bicategory,
where the two sides only differ by replacing strings of bicategory structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `bicategory` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `bicategory_coherence`.
-/
def bicategory (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.main  Bicategory.Context `bicategory mvarId

@[inherit_doc bicategory]
elab "bicategory" : tactic => withMainContext do
  replaceMainGoal <| ← bicategory <| ← getMainGoal

end Mathlib.Tactic.Bicategory
