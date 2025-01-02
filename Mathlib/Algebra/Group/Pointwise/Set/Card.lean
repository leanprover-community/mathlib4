/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of pointwise operations on sets
-/

open scoped Cardinal Pointwise

namespace Set
variable {G M α : Type*}

section Mul
variable [Mul M] {s t : Set M}

@[to_additive]
lemma _root_.Cardinal.mk_mul_le : #(s * t) ≤ #s * #t := by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

variable [IsCancelMul M]

@[to_additive]
lemma natCard_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  simp only [Nat.card, ← Cardinal.toNat_mul]
  refine Cardinal.toNat_le_toNat Cardinal.mk_mul_le ?_
  aesop (add simp [Cardinal.mul_lt_aleph0_iff, finite_mul])

@[to_additive] alias card_mul_le := natCard_mul_le

-- `alias` doesn't add the deprecation suggestion to the `to_additive` version
-- see https://github.com/leanprover-community/mathlib4/issues/19424
attribute [deprecated natCard_mul_le (since := "2024-09-30")] card_mul_le
attribute [deprecated natCard_add_le (since := "2024-09-30")] card_add_le


end Mul

section InvolutiveInv
variable [InvolutiveInv G]

@[to_additive (attr := simp)]
lemma _root_.Cardinal.mk_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv_eq_inv, Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]
lemma natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv_eq_inv, Nat.card_image_of_injective inv_injective]

@[to_additive] alias card_inv := natCard_inv

-- `alias` doesn't add the deprecation suggestion to the `to_additive` version
-- see https://github.com/leanprover-community/mathlib4/issues/19424
attribute [deprecated natCard_inv (since := "2024-09-30")] card_inv
attribute [deprecated natCard_neg (since := "2024-09-30")] card_neg

@[to_additive (attr := simp)]
lemma encard_inv (s : Set G) : s⁻¹.encard = s.encard := by simp [encard, ENat.card]

@[to_additive (attr := simp)]
lemma ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard := by simp [ncard]

end InvolutiveInv

section DivInvMonoid
variable [DivInvMonoid M] {s t : Set M}

@[to_additive]
lemma _root_.Cardinal.mk_div_le : #(s / t) ≤ #s * #t := by
  rw [← image2_div]; exact Cardinal.mk_image2_le

end DivInvMonoid

section Group
variable [Group G] {s t : Set G}

@[to_additive]
lemma natCard_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← natCard_inv t]; exact natCard_mul_le

@[to_additive] alias card_div_le := natCard_div_le

-- `alias` doesn't add the deprecation suggestion to the `to_additive` version
-- see https://github.com/leanprover-community/mathlib4/issues/19424
attribute [deprecated natCard_div_le (since := "2024-09-30")] card_div_le
attribute [deprecated natCard_sub_le (since := "2024-09-30")] card_sub_le

variable [MulAction G α]

@[to_additive (attr := simp)]
lemma _root_.Cardinal.mk_smul_set (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]
lemma natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

@[to_additive]
alias card_smul_set := Cardinal.mk_smul_set

-- `alias` doesn't add the deprecation suggestion to the `to_additive` version
-- see https://github.com/leanprover-community/mathlib4/issues/19424
attribute [deprecated Cardinal.mk_smul_set (since := "2024-09-30")] card_smul_set
attribute [deprecated Cardinal.mk_vadd_set (since := "2024-09-30")] card_vadd_set

@[to_additive (attr := simp)]
lemma encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard := by
  simp [encard, ENat.card]

@[to_additive (attr := simp)]
lemma ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard := by simp [ncard]

end Group
end Set
