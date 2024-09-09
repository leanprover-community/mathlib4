/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Pointwise.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of pointwise operations on sets.
-/

namespace Set

open Pointwise

variable {α β : Type*}

section MulAction
variable [Group α] [MulAction α β]

@[to_additive (attr := simp)]
lemma card_smul_set (a : α) (s : Set β) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

end MulAction

section IsCancelMul
variable [Mul α] [IsCancelMul α] {s t : Set α}

@[to_additive]
lemma card_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  classical
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  obtain ⟨hs, ht⟩ | rfl | rfl := finite_mul.1 h
  · lift s to Finset α using hs
    lift t to Finset α using ht
    rw [← Finset.coe_mul]
    simpa [-Finset.coe_mul] using Finset.card_mul_le
  all_goals simp

end IsCancelMul

section InvolutiveInv
variable [InvolutiveInv α] {s t : Set α}

@[to_additive (attr := simp)]
lemma card_inv (s : Set α) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

end InvolutiveInv

section Group
variable [Group α] {s t : Set α}

@[to_additive]
lemma card_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← card_inv t]; exact card_mul_le

end Group
end Set
