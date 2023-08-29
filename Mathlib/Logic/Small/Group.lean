/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Transfer group structures from `α` to `Shrink α`.
-/

set_option autoImplicit true

noncomputable section

-- FIXME: here and below, why doesn't `to_additive` work?
-- We're waiting on the fix for https://github.com/leanprover/lean4/issues/2077 to arrive.

instance [Zero α] [Small α] : Zero (Shrink α) := (equivShrink _).symm.zero

@[to_additive existing]
instance [One α] [Small α] : One (Shrink α) := (equivShrink _).symm.one

@[simp]
lemma equivShrink_symm_zero [Zero α] [Small α] : (equivShrink α).symm 0 = 0 :=
  (equivShrink α).symm_apply_apply 0

@[to_additive existing (attr := simp)]
lemma equivShrink_symm_one [One α] [Small α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1

instance [Add α] [Small α] : Add (Shrink α) := (equivShrink _).symm.add

@[to_additive existing]
instance [Mul α] [Small α] : Mul (Shrink α) := (equivShrink _).symm.mul

@[simp]
lemma equivShrink_symm_add [Add α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x + y) = (equivShrink α).symm x + (equivShrink α).symm y := by
  rw [Equiv.add_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (↑(equivShrink α).symm x + …
  simp
  -- 🎉 no goals

@[simp]
lemma equivShrink_add [Add α] [Small α] (x y : α) :
    equivShrink α (x + y) = equivShrink α x + equivShrink α y := by
  rw [Equiv.add_def]
  -- ⊢ ↑(equivShrink α) (x + y) = ↑(equivShrink α).symm.symm (↑(equivShrink α).symm …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_symm_mul [Mul α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  rw [Equiv.mul_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (↑(equivShrink α).symm x * …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_mul [Mul α] [Small α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  rw [Equiv.mul_def]
  -- ⊢ ↑(equivShrink α) (x * y) = ↑(equivShrink α).symm.symm (↑(equivShrink α).symm …
  simp
  -- 🎉 no goals

instance [Sub α] [Small α] : Sub (Shrink α) := (equivShrink _).symm.sub

@[to_additive existing]
instance [Div α] [Small α] : Div (Shrink α) := (equivShrink _).symm.div

@[simp]
lemma equivShrink_symm_sub [Sub α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x - y) = (equivShrink α).symm x - (equivShrink α).symm y := by
  rw [Equiv.sub_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (↑(equivShrink α).symm x - …
  simp
  -- 🎉 no goals

@[simp]
lemma equivShrink_sub [Sub α] [Small α] (x y : α) :
    equivShrink α (x - y) = equivShrink α x - equivShrink α y := by
  rw [Equiv.sub_def]
  -- ⊢ ↑(equivShrink α) (x - y) = ↑(equivShrink α).symm.symm (↑(equivShrink α).symm …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_symm_div [Div α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  rw [Equiv.div_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (↑(equivShrink α).symm x / …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_div [Div α] [Small α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  rw [Equiv.div_def]
  -- ⊢ ↑(equivShrink α) (x / y) = ↑(equivShrink α).symm.symm (↑(equivShrink α).symm …
  simp
  -- 🎉 no goals

instance [Neg α] [Small α] : Neg (Shrink α) := (equivShrink _).symm.Neg

@[to_additive existing]
instance [Inv α] [Small α] : Inv (Shrink α) := (equivShrink _).symm.Inv

@[simp]
lemma equivShrink_symm_neg [Neg α] [Small α] (x : Shrink α) :
    (equivShrink α).symm (-x) = -(equivShrink α).symm x := by
  rw [Equiv.neg_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (-↑(equivShrink α).symm x) …
  simp
  -- 🎉 no goals

@[simp]
lemma equivShrink_neg [Neg α] [Small α] (x : α) :
    equivShrink α (-x) = -equivShrink α x := by
  rw [Equiv.neg_def]
  -- ⊢ ↑(equivShrink α) (-x) = ↑(equivShrink α).symm.symm (-↑(equivShrink α).symm ( …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_symm_inv [Inv α] [Small α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  rw [Equiv.inv_def]
  -- ⊢ ↑(equivShrink α).symm (↑(equivShrink α).symm.symm (↑(equivShrink α).symm x)⁻ …
  simp
  -- 🎉 no goals

@[to_additive existing (attr := simp)]
lemma equivShrink_inv [Inv α] [Small α] (x : α) :
    equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  rw [Equiv.inv_def]
  -- ⊢ ↑(equivShrink α) x⁻¹ = ↑(equivShrink α).symm.symm (↑(equivShrink α).symm (↑( …
  simp
  -- 🎉 no goals

instance [AddSemigroup α] [Small α] : AddSemigroup (Shrink α) := (equivShrink _).symm.addSemigroup

@[to_additive existing]
instance [Semigroup α] [Small α] : Semigroup (Shrink α) := (equivShrink _).symm.semigroup

instance [SemigroupWithZero α] [Small α] : SemigroupWithZero (Shrink α) :=
  (equivShrink _).symm.semigroupWithZero

instance [AddCommSemigroup α] [Small α] : AddCommSemigroup (Shrink α) :=
  (equivShrink _).symm.addCommSemigroup

@[to_additive existing]
instance [CommSemigroup α] [Small α] : CommSemigroup (Shrink α) :=
  (equivShrink _).symm.commSemigroup

instance [MulZeroClass α] [Small α] : MulZeroClass (Shrink α) :=
  (equivShrink _).symm.mulZeroClass

instance [AddZeroClass α] [Small α] : AddZeroClass (Shrink α) :=
  (equivShrink _).symm.addZeroClass

@[to_additive existing]
instance [MulOneClass α] [Small α] : MulOneClass (Shrink α) :=
  (equivShrink _).symm.mulOneClass

instance [MulZeroOneClass α] [Small α] : MulZeroOneClass (Shrink α) :=
  (equivShrink _).symm.mulZeroOneClass

instance [AddMonoid α] [Small α] : AddMonoid (Shrink α) :=
  (equivShrink _).symm.addMonoid

@[to_additive existing]
instance [Monoid α] [Small α] : Monoid (Shrink α) :=
  (equivShrink _).symm.monoid

instance [AddCommMonoid α] [Small α] : AddCommMonoid (Shrink α) :=
  (equivShrink _).symm.addCommMonoid

@[to_additive existing]
instance [CommMonoid α] [Small α] : CommMonoid (Shrink α) :=
  (equivShrink _).symm.commMonoid

instance [AddGroup α] [Small α] : AddGroup (Shrink α) :=
  (equivShrink _).symm.addGroup

@[to_additive existing]
instance [Group α] [Small α] : Group (Shrink α) :=
  (equivShrink _).symm.group

instance [AddCommGroup α] [Small α] : AddCommGroup (Shrink α) :=
  (equivShrink _).symm.addCommGroup

@[to_additive existing]
instance [CommGroup α] [Small α] : CommGroup (Shrink α) :=
  (equivShrink _).symm.commGroup
