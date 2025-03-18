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

-- TODO
-- assert_not_exists Ring
assert_not_exists MulAction

open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq β]

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
