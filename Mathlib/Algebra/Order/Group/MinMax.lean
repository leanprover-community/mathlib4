/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.MinMax

#align_import algebra.order.group.min_max from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# `min` and `max` in linearly ordered groups.
-/


section

variable {α : Type*} [Group α] [LinearOrder α] [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive (attr := simp)]
theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_total a 1 with (h | h) <;> simp [h]
  -- ⊢ max a 1 / max a⁻¹ 1 = a
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align max_one_div_max_inv_one_eq_self max_one_div_max_inv_one_eq_self
#align max_zero_sub_max_neg_zero_eq_self max_zero_sub_max_neg_zero_eq_self

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self
#align max_zero_sub_eq_self max_zero_sub_eq_self

end

section LinearOrderedCommGroup

variable {α : Type*} [LinearOrderedCommGroup α] {a b c : α}

@[to_additive min_neg_neg]
theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
  -- Porting note: Explicit `α` necessary to infer `CovariantClass` instance
    (@inv_le_inv_iff α _ _ _).mpr
#align min_inv_inv' min_inv_inv'
#align min_neg_neg min_neg_neg

@[to_additive max_neg_neg]
theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
  -- Porting note: Explicit `α` necessary to infer `CovariantClass` instance
    (@inv_le_inv_iff α _ _ _).mpr
#align max_inv_inv' max_inv_inv'
#align max_neg_neg max_neg_neg

@[to_additive min_sub_sub_right]
theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹
  -- 🎉 no goals
#align min_div_div_right' min_div_div_right'
#align min_sub_sub_right min_sub_sub_right

@[to_additive max_sub_sub_right]
theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹
  -- 🎉 no goals
#align max_div_div_right' max_div_div_right'
#align max_sub_sub_right max_sub_sub_right

@[to_additive min_sub_sub_left]
theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']
  -- 🎉 no goals
#align min_div_div_left' min_div_div_left'
#align min_sub_sub_left min_sub_sub_left

@[to_additive max_sub_sub_left]
theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']
  -- 🎉 no goals
#align max_div_div_left' max_div_div_left'
#align max_sub_sub_left max_sub_sub_left

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable {α : Type*} [LinearOrderedAddCommGroup α] {a b c : α}

theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
  simp only [sub_le_iff_le_add, max_le_iff]; constructor
  -- ⊢ a ≤ max (a - c) (b - d) + max c d ∧ b ≤ max (a - c) (b - d) + max c d
                                             -- ⊢ a ≤ max (a - c) (b - d) + max c d
  calc
    a = a - c + c := (sub_add_cancel a c).symm
    _ ≤ max (a - c) (b - d) + max c d := add_le_add (le_max_left _ _) (le_max_left _ _)
  calc
    b = b - d + d := (sub_add_cancel b d).symm
    _ ≤ max (a - c) (b - d) + max c d := add_le_add (le_max_right _ _) (le_max_right _ _)
#align max_sub_max_le_max max_sub_max_le_max

theorem abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| ≤ max |a - c| |b - d| := by
  refine' abs_sub_le_iff.2 ⟨_, _⟩
  -- ⊢ max a b - max c d ≤ max |a - c| |b - d|
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
    -- 🎉 no goals
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    -- ⊢ max c d - max a b ≤ max |c - a| |d - b|
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
    -- 🎉 no goals
#align abs_max_sub_max_le_max abs_max_sub_max_le_max

theorem abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| ≤ max |a - c| |b - d| := by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)
#align abs_min_sub_min_le_max abs_min_sub_min_le_max

theorem abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| ≤ |a - b| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c
#align abs_max_sub_max_le_abs abs_max_sub_max_le_abs

end LinearOrderedAddCommGroup
