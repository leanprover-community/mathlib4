/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

assert_not_exists MulAction Ring

open scoped Pointwise

namespace Finset
variable {α : Type*}

section Mul

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

lemma card_le_card_mul_left₀ [IsLeftCancelMulZero α] (has : a ∈ s) (ha : a ≠ 0) : #t ≤ #(s * t) :=
  card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

lemma card_le_card_mul_right₀ [IsRightCancelMulZero α] (hat : a ∈ t) (ha : a ≠ 0) : #s ≤ #(s * t) :=
  card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

lemma card_le_card_mul_self₀ [IsLeftCancelMulZero α] : #s ≤ #(s * s) := by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact card_le_card_mul_left₀ ha.2 ha.1

end Mul

section MulZeroClass
variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

/-! Note that `Finset` is not a `MulZeroClass` because `0 * ∅ ≠ 0`. -/

lemma mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
lemma zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

lemma Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs

lemma Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs

end MulZeroClass

section GroupWithZero
variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

lemma div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]

lemma zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]

lemma Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs

lemma Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs

@[simp] protected lemma inv_zero : (0 : Finset α)⁻¹ = 0 := by ext; simp

end GroupWithZero
end Finset
