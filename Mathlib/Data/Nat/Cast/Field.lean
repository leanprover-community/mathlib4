/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.CharZero
import Mathlib.Data.Nat.Cast.Basic

#align_import data.nat.cast.field from "leanprover-community/mathlib"@"acee671f47b8e7972a1eb6f4eed74b4b3abce829"

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

 * `Nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
 * `Nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/


namespace Nat

variable {α : Type*}

@[simp]
theorem cast_div [DivisionSemiring α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
    ((m / n : ℕ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  -- ⊢ ↑(n * k / n) = ↑(n * k) / ↑n
  have : n ≠ 0 := by
    rintro rfl
    simp at n_nonzero
  rw [Nat.mul_div_cancel_left _ this.bot_lt, mul_comm n k,cast_mul, mul_div_cancel _ n_nonzero]
  -- 🎉 no goals
#align nat.cast_div Nat.cast_div

theorem cast_div_div_div_cancel_right [DivisionSemiring α] [CharZero α] {m n d : ℕ}
  (hn : d ∣ n) (hm : d ∣ m) :
    (↑(m / d) : α) / (↑(n / d) : α) = (m : α) / n := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp hm]
  -- ⊢ ↑(m / 0) / ↑(n / 0) = ↑m / ↑n
                                         -- 🎉 no goals
  replace hd : (d : α) ≠ 0;
  -- ⊢ ↑d ≠ 0
  · norm_cast
    -- 🎉 no goals
  rw [cast_div hm, cast_div hn, div_div_div_cancel_right _ hd] <;> exact hd
  -- ⊢ ↑d ≠ 0
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align nat.cast_div_div_div_cancel_right Nat.cast_div_div_div_cancel_right

section LinearOrderedSemifield

variable [LinearOrderedSemifield α]

/-- Natural division is always less than division in the field. -/
theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n := by
  cases n
  -- ⊢ ↑(m / zero) ≤ ↑m / ↑zero
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
    -- 🎉 no goals
  rw [le_div_iff, ← Nat.cast_mul, @Nat.cast_le]
  -- ⊢ m / succ n✝ * succ n✝ ≤ m
  exact (Nat.div_mul_le_self m _)
  -- ⊢ 0 < ↑(succ n✝)
  · exact Nat.cast_pos.2 (Nat.succ_pos _)
    -- 🎉 no goals
#align nat.cast_div_le Nat.cast_div_le

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one
#align nat.inv_pos_of_nat Nat.inv_pos_of_nat

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  -- ⊢ 0 < (↑n + 1)⁻¹
  exact inv_pos_of_nat
  -- 🎉 no goals
#align nat.one_div_pos_of_nat Nat.one_div_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine' one_div_le_one_div_of_le _ _
  -- ⊢ 0 < ↑n + 1
  exact Nat.cast_add_one_pos _
  -- ⊢ ↑n + 1 ≤ ↑m + 1
  simpa
  -- 🎉 no goals
#align nat.one_div_le_one_div Nat.one_div_le_one_div

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine' one_div_lt_one_div_of_lt _ _
  -- ⊢ 0 < ↑n + 1
  exact Nat.cast_add_one_pos _
  -- ⊢ ↑n + 1 < ↑m + 1
  simpa
  -- 🎉 no goals
#align nat.one_div_lt_one_div Nat.one_div_lt_one_div

end LinearOrderedSemifield

end Nat
