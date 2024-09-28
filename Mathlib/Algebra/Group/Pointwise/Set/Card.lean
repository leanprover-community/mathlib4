/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pointwise.Finite
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
lemma card_mul_le : #(s * t) ≤ #s * #t := by rw [← image2_mul]; exact Cardinal.mk_image2_le

variable [IsCancelMul M]

@[to_additive]
lemma natCard_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  classical
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  obtain ⟨hs, ht⟩ | rfl | rfl := finite_mul.1 h
  · unfold Nat.card
    rw [← Cardinal.toNat_mul]
    gcongr
    · exact Cardinal.mul_lt_aleph0 hs.lt_aleph0 ht.lt_aleph0
    · exact card_mul_le
  all_goals simp

end Mul

section InvolutiveInv
variable [InvolutiveInv G] {s t : Set G}

@[to_additive (attr := simp)]
lemma card_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv, Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]
lemma natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

end InvolutiveInv

section DivisionMonoid
variable [DivisionMonoid M] {s t : Set M}

@[to_additive]
lemma card_div_le : #(s / t) ≤ #s * #t := by
  rw [div_eq_mul_inv, ← card_inv t]; exact card_mul_le

end DivisionMonoid

section Group
variable [Group G] {s t : Set G}

@[to_additive]
lemma natCard_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← natCard_inv t]; exact natCard_mul_le

variable [MulAction G α]

@[to_additive (attr := simp)]
lemma card_smul_set (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]
lemma natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

end Group
end Set
