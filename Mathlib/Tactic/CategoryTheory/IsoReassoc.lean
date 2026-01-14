/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Iso

/-!
# Extension of `reassoc` to isomorphisms.

We extend `reassoc` and `reassoc_of%` for equality of isomorphisms.
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ≅ Y` in some category will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`
but with the conclusions simplified using basic proportions in isomorphisms in a category
(`Iso.trans_refl`, `Iso.refl_trans`, `Iso.trans_assoc`, `Iso.trans_symm`,
`Iso.symm_self_id` and `Iso.self_symm_id`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace CategoryTheory

variable {C : Type*} [Category C]

theorem Iso.eq_whisker {X Y : C} {f g : X ≅ Y} (w : f = g) {Z : C} (h : Y ≅ Z) :
    f ≪≫ h = g ≪≫ h := by rw [w]

/-- Simplify an expression using only the axioms of a groupoid. -/
def categoryIsoSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decide := false })

/--
Given an equation `f = g` between isomorphisms `X ≅ Y` in a category,
produce the equation `∀ {Z} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`,
but with compositions fully right associated, identities removed, and functors applied.
-/
def reassocExprIso (e : Expr) : MetaM Expr := do
  simpType categoryIsoSimp (← mkAppM ``Iso.eq_whisker #[e])

initialize registerReassocExpr reassocExprIso

end CategoryTheory
