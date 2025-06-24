/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Cast

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

* `Int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/


namespace Int

open Nat

variable {α : Type*}

/-- Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `DivisionRing` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
theorem cast_neg_natCast {R} [DivisionRing R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp

@[simp]
theorem cast_div [DivisionRing α] {m n : ℤ} (n_dvd : n ∣ m) (hn : (n : α) ≠ 0) :
    ((m / n : ℤ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by rintro rfl; simp at hn
  rw [Int.mul_ediv_cancel_left _ this, mul_comm n, Int.cast_mul, mul_div_cancel_right₀ _ hn]

theorem cast_div_le [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ℤ}
    (hn : 0 ≤ n) :
    ((m / n : ℤ) : α) ≤ (m : α) / (n : α) := by
  by_cases hn_zero : n = 0
  · simp [hn_zero]
  replace hn : 0 < n := by omega
  rw [le_div_iff₀, ← Int.cast_mul, Int.cast_le]
  · exact Int.ediv_mul_le m hn_zero
  · exact cast_pos.mpr hn

end Int
