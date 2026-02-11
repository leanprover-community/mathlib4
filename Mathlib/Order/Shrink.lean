/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Logic.Small.Defs

/-!
# Order instances on Shrink

If `α : Type v` is `u`-small, we transport various order related
instances on `α` to `Shrink.{u} α`.

-/

@[expose] public section

universe u

variable {α : Type*} [Small.{u} α]

section Bot
variable [Bot α]

@[to_dual]
noncomputable instance : Bot (Shrink.{u} α) where
  bot := equivShrink _ ⊥

@[to_dual (attr := simp)]
lemma equivShrink_bot : equivShrink.{u} α ⊥ = ⊥ := rfl

@[to_dual (attr := simp)]
lemma equivShrink_symm_bot : (equivShrink.{u} α).symm ⊥ = ⊥ :=
  (equivShrink.{u} α).injective (by simp)

end Bot

section Preorder
variable [Preorder α]

instance : Preorder (Shrink.{u} α) :=
  Preorder.lift (equivShrink α).symm

variable (α) in
/-- The order isomorphism `α ≃o Shrink.{u} α`. -/
noncomputable def orderIsoShrink : α ≃o Shrink.{u} α where
  toEquiv := equivShrink α
  map_rel_iff' {a b} := by
    obtain ⟨a, rfl⟩ := (equivShrink.{u} α).symm.surjective a
    obtain ⟨b, rfl⟩ := (equivShrink.{u} α).symm.surjective b
    simp only [Equiv.apply_symm_apply]
    rfl

@[simp]
lemma orderIsoShrink_apply (a : α) :
    orderIsoShrink α a = equivShrink α a := rfl

@[simp]
lemma orderIsoShrink_symm_apply (a : Shrink.{u} α) :
    (orderIsoShrink α).symm a = (equivShrink α).symm a := rfl

@[simp]
theorem equivShrink_le_equivShrink {x y : α} : equivShrink α x ≤ equivShrink α y ↔ x ≤ y :=
  (orderIsoShrink α).map_rel_iff

@[simp]
theorem equivShrink_lt_equivShrink {x y : α} : equivShrink α x < equivShrink α y ↔ x < y :=
  (orderIsoShrink α).toRelIsoLT.map_rel_iff

@[to_dual]
noncomputable instance [OrderBot α] : OrderBot (Shrink.{u} α) where
  bot_le a := by simp [← (orderIsoShrink.{u} α).symm.le_iff_le]

@[to_dual]
noncomputable instance [SuccOrder α] : SuccOrder (Shrink.{u} α) :=
  SuccOrder.ofOrderIso (orderIsoShrink.{u} α)

instance [WellFoundedLT α] : WellFoundedLT (Shrink.{u} α) where
  wf := (orderIsoShrink.{u} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

@[to_dual existing]
instance [WellFoundedGT α] : WellFoundedGT (Shrink.{u} α) where
  wf := (orderIsoShrink.{u} α).symm.dual.toRelIsoLT.toRelEmbedding.isWellFounded.wf

end Preorder

instance [PartialOrder α] : PartialOrder (Shrink.{u} α) :=
  (equivShrink _).symm.injective.partialOrder _ .rfl .rfl

noncomputable instance [LinearOrder α] : LinearOrder (Shrink.{u} α) :=
  .lift' _ (equivShrink _).symm.injective
