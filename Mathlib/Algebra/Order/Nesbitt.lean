/-
Copyright (c) 2026 Brandon Frederick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brandon Frederick
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-!
# Nesbitt's inequality

This file proves Nesbitt's inequality: for positive elements `a`, `b`, `c` of a linearly
ordered field,

`3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b)`,

together with its equality case: the sum equals `3 / 2` exactly when `a = b = c`.

The proof clears denominators and reduces to the sum-of-squares identity
`(a + b) * (a - b) ^ 2 + (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 ≥ 0`.

## Main declarations

* `nesbitt_inequality`: Nesbitt's inequality.
* `nesbitt_inequality_eq_iff`: the equality case of Nesbitt's inequality.
-/

public section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : K}

/-- **Nesbitt's inequality**: for positive elements `a`, `b`, `c` of a linearly ordered
field, `3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b)`. -/
theorem nesbitt_inequality (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have hbc : (0 : K) < b + c := by linarith
  have hca : (0 : K) < c + a := by linarith
  have hab : (0 : K) < a + b := by linarith
  rw [show a / (b + c) + b / (c + a) + c / (a + b)
        = (a * ((c + a) * (a + b)) + b * ((b + c) * (a + b)) + c * ((b + c) * (c + a)))
          / ((b + c) * ((c + a) * (a + b))) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

/-- **Equality case of Nesbitt's inequality**: for positive elements `a`, `b`, `c` of a
linearly ordered field, `a / (b + c) + b / (c + a) + c / (a + b) = 3 / 2` holds exactly
when `a = b = c`. -/
theorem nesbitt_inequality_eq_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) = 3 / 2 ↔ a = b ∧ b = c := by
  have hbc : (0 : K) < b + c := by linarith
  have hca : (0 : K) < c + a := by linarith
  have hab : (0 : K) < a + b := by linarith
  constructor
  · intro h
    rw [show a / (b + c) + b / (c + a) + c / (a + b)
          = (a * ((c + a) * (a + b)) + b * ((b + c) * (a + b)) + c * ((b + c) * (c + a)))
            / ((b + c) * ((c + a) * (a + b))) by field_simp] at h
    rw [div_eq_div_iff (by positivity) (by norm_num)] at h
    have key : (a + b) * (a - b) ^ 2 + (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 = 0 := by
      linear_combination h
    have t1 : 0 ≤ (a + b) * (a - b) ^ 2 := by positivity
    have t2 : 0 ≤ (b + c) * (b - c) ^ 2 := by positivity
    have t3 : 0 ≤ (c + a) * (c - a) ^ 2 := by positivity
    have e1 : (a + b) * (a - b) ^ 2 = 0 := by linarith
    have e2 : (b + c) * (b - c) ^ 2 = 0 := by linarith
    have hab' : a = b := by
      rcases mul_eq_zero.mp e1 with h' | h'
      · exact absurd h' (by positivity)
      · have hs := sq_eq_zero_iff.mp h'
        linarith
    have hbc' : b = c := by
      rcases mul_eq_zero.mp e2 with h' | h'
      · exact absurd h' (by positivity)
      · have hs := sq_eq_zero_iff.mp h'
        linarith
    exact ⟨hab', hbc'⟩
  · rintro ⟨rfl, rfl⟩
    have h2 : a + a ≠ 0 := by positivity
    field_simp
    norm_num
