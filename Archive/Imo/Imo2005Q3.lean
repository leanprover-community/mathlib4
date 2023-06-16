/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales

! This file was ported from Lean 3 source module imo.imo2005_q3
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# IMO 2005 Q3
Let `x`, `y` and `z` be positive real numbers such that `xyz ≥ 1`. Prove that:
`(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(y^5 + z^2 + x^2) + (z^5 - z^2)/(z^5 + x^2 + y^2) ≥ 0`

# Solution
The solution by Iurie Boreico from Moldova is presented, which won a special prize during the exam.
The key insight is that `(x^5-x^2)/(x^5+y^2+z^2) ≥ (x^2-y*z)/(x^2+y^2+z^2)`, which is proven by
factoring `(x^5-x^2)/(x^5+y^2+z^2) - (x^5-x^2)/(x^3*(x^2+y^2+z^2))` into a non-negative expression
and then making use of `xyz ≥ 1` to show `(x^5-x^2)/(x^3*(x^2+y^2+z^2)) ≥ (x^2-y*z)/(x^2+y^2+z^2)`.
-/


namespace imo2005_q3

theorem key_insight (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h₁ : 0 < x ^ 5 + y ^ 2 + z ^ 2 := by positivity
  have h₂ : 0 < x ^ 3 := by positivity
  have h₃ : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have h₄ : 0 < x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by positivity
  have key :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) -
        (x ^ 5 - x ^ 2) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) =
      (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /
        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) := by
    field_simp [h₁.ne', h₄.ne']
    ring
  have h₅ :
    (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /
        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) ≥
      0 :=
    by positivity
  calc
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥
        (x ^ 5 - x ^ 2) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) :=
      by linarith [key, h₅]
    _ ≥ (x ^ 5 - x ^ 2 * (x * y * z)) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by
      refine' (div_le_div_right h₄).mpr _; simp only [sub_le_sub_iff_left]
      exact (le_mul_iff_one_le_right (pow_pos hx 2)).mpr h
    _ = (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by field_simp [h₂.ne', h₃.ne']; ring
#align imo2005_q3.key_insight Imo2005Q3.key_insight

end imo2005_q3

open imo2005_q3

theorem imo2005_q3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
        (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥
      0 := by
  calc
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
          (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥
        (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) + (y ^ 2 - z * x) / (y ^ 2 + z ^ 2 + x ^ 2) +
          (z ^ 2 - x * y) / (z ^ 2 + x ^ 2 + y ^ 2) := by
      linarith [key_insight x y z hx hy hz h, key_insight y z x hy hz hx (by linarith [h]),
        key_insight z x y hz hx hy (by linarith [h])]
    _ = 1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by
      have h₁ : y ^ 2 + z ^ 2 + x ^ 2 = x ^ 2 + y ^ 2 + z ^ 2; ring
      have h₂ : z ^ 2 + x ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 + z ^ 2; ring
      rw [h₁, h₂]; ring
    _ ≥ 0 :=
      div_nonneg (by linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)])
        (by linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z])
#align imo2005_q3 imo2005_q3
