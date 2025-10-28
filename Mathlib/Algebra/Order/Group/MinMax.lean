/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# `min` and `max` in linearly ordered groups.
-/


section

variable {α : Type*} [Group α] [LinearOrder α] [MulLeftMono α]

-- TODO: This duplicates `oneLePart_div_leOnePart`
@[to_additive (attr := simp)]
theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

@[to_additive]
lemma max_inv_one (a : α) : max a⁻¹ 1 = a⁻¹ * max a 1 := by
  rw [eq_inv_mul_iff_mul_eq, ← eq_div_iff_mul_eq', max_one_div_max_inv_one_eq_self]

end

section LinearOrderedCommGroup

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive min_neg_neg]
theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]
theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]
theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]
theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
  grind

theorem abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| ≤ max |a - c| |b - d| := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))

theorem abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| ≤ max |a - c| |b - d| := by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

theorem abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| ≤ |a - b| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c

end LinearOrderedAddCommGroup
