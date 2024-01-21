/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Real.Sqrt

/-!
# IMO 1960 Q2

For what values of the variable $x$ does the following inequality hold:

\[\dfrac{4x^2}{(1 - \sqrt {2x + 1})^2} < 2x + 9 \ ?\]
-/

open Real Set

namespace Imo1960Q2

def IsGood (x : ℝ) : Prop :=
  4 * x ^ 2 / (1 - sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 ∧ 0 ≤ 2 * x + 1 ∧
    (1 - sqrt (2 * x + 1)) ^ 2 ≠ 0

theorem isGood_iff {x} : IsGood x ↔ x ∈ Ico (-1/2) (45/8) \ {0} := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [IsGood]
  cases lt_or_le x (-1/2) with
  | inl hx2 =>
    have : 2 * x + 1 < 0 := by linarith
    simp [hx2.not_le, IsGood, this.not_le]
  | inr hx2 =>
    have hx2' : 0 ≤ 2 * x + 1 := by linarith
    have H : 1 - sqrt (2 * x + 1) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, sqrt_eq_iff_sq_eq hx2' zero_le_one]
      simpa
    suffices 4 * x ^ 2 < (2 * x + 9) * (1 - sqrt (2 * x + 1)) ^ 2 ↔ x < 45 / 8 by
      simp [IsGood, div_lt_iff ((sq_pos_iff _).2 H), *]
    rw [sub_sq, sq_sqrt hx2', ← sub_pos]
    set a := sqrt (2 * x + 1) with ha
    have ha₀ : 0 ≤ a := sqrt_nonneg _
    clear_value a
    have hxa : x = (a ^ 2 - 1) / 2 := by field_simp [ha, sq_sqrt hx2', mul_comm x]
    rw [hxa]
    suffices 0 < (1 - a) ^ 2 * (7 - 2 * a) ↔ a ^ 2 < (7 / 2) ^ 2 by
      rw [div_lt_iff two_pos, sub_lt_iff_lt_add]
      convert this using 2 <;> ring_nf
    rw [mul_pos_iff_of_pos_left ((sq_pos_iff _).2 H), pow_lt_pow_iff_left, sub_pos,
      lt_div_iff'] <;> positivity
