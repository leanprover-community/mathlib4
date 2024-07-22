/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Common
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

 * `Nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/


namespace Nat

variable {α : Type*}

@[simp]
theorem cast_div [DivisionSemiring α] {m n : ℕ} (n_dvd : n ∣ m) (hn : (n : α) ≠ 0) :
    ((m / n : ℕ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ <| zero_lt_of_ne_zero this, mul_comm n,
    cast_mul, mul_div_cancel_right₀ _ hn]

theorem cast_div_div_div_cancel_right [DivisionSemiring α] [CharZero α] {m n d : ℕ}
    (hn : d ∣ n) (hm : d ∣ m) :
    (↑(m / d) : α) / (↑(n / d) : α) = (m : α) / n := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : α) ≠ 0 := by norm_cast
  rw [cast_div hm, cast_div hn, div_div_div_cancel_right _ hd] <;> exact hd

end Nat
