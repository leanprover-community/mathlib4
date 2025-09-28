/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
import Mathlib.Algebra.Order.Field.Basic

/-!
# Cast of naturals into ordered fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a `LinearOrderedSemifield`.

## Main results

* `Nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/


namespace Nat

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

lemma cast_inv_le_one : ∀ n : ℕ, (n⁻¹ : α) ≤ 1
  | 0 => by simp
  | n + 1 => inv_le_one_of_one_le₀ <| by simp [Nat.cast_nonneg]

/-- Natural division is always less than division in the field. -/
theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n := by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
  rw [le_div_iff₀, ← Nat.cast_mul, @Nat.cast_le]
  · exact Nat.div_mul_le_self m _
  · exact Nat.cast_pos.2 (Nat.succ_pos _)

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_cast_pos {n : ℕ} (hn : n ≠ 0) : 0 < 1 / (n : α) :=
  one_div_pos.mpr (cast_pos.mpr (Nat.pos_of_ne_zero hn))

theorem one_div_cast_nonneg (n : ℕ) : 0 ≤ 1 / (n : α) := one_div_nonneg.mpr (cast_nonneg' n)

theorem one_div_cast_ne_zero {n : ℕ} (hn : n ≠ 0) : 1 / (n : α) ≠ 0 :=
  _root_.ne_of_gt (one_div_cast_pos hn)

end Nat
