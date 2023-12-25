/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Polyrith

#align_import imo.imo2006_q3 from "leanprover-community/mathlib"@"308826471968962c6b59c7ff82a22757386603e3"

/-!
# IMO 2006 Q3

Determine the least real number $M$ such that
$$
\left| ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2) \right|
≤ M (a^2 + b^2 + c^2)^2
$$
for all real numbers $a$, $b$, $c$.

## Solution

The answer is $M = \frac{9 \sqrt 2}{32}$.

This is essentially a translation of the solution in
https://web.evanchen.cc/exams/IMO-2006-notes.pdf.

It involves making the substitution
`x = a - b`, `y = b - c`, `z = c - a`, `s = a + b + c`.
-/


open Real

namespace Imo2006Q3

/-- Replacing `x` and `y` with their average increases the left side. -/
theorem lhs_ineq {x y : ℝ} (hxy : 0 ≤ x * y) :
    16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 3 := by
  have : (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y)) ≥ 0 := by positivity
  calc 16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 2 * (x + y) ^ 2 := by gcongr; linarith
    _ = ((x + y) ^ 2) ^ 3 := by ring
#align imo2006_q3.lhs_ineq Imo2006Q3.lhs_ineq

theorem four_pow_four_pos : (0 : ℝ) < 4 ^ 4 := by norm_num
#align imo2006_q3.four_pow_four_pos Imo2006Q3.four_pow_four_pos

theorem mid_ineq {s t : ℝ} : s * t ^ 3 ≤ (3 * t + s) ^ 4 / 4 ^ 4 := by
  rw [le_div_iff four_pow_four_pos]
  have : 0 ≤ (s - t) ^ 2 * ((s + 7 * t) ^ 2 + 2 * (4 * t) ^ 2) := by positivity
  linarith
#align imo2006_q3.mid_ineq Imo2006Q3.mid_ineq

/-- Replacing `x` and `y` with their average decreases the right side. -/
theorem rhs_ineq {x y : ℝ} : 3 * (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) := by
  have : 0 ≤ (x - y) ^ 2 := by positivity
  linarith
#align imo2006_q3.rhs_ineq Imo2006Q3.rhs_ineq

theorem zero_lt_32 : (0 : ℝ) < 32 := by norm_num
#align imo2006_q3.zero_lt_32 Imo2006Q3.zero_lt_32

theorem subst_wlog {x y z s : ℝ} (hxy : 0 ≤ x * y) (hxyz : x + y + z = 0) :
    32 * |x * y * z * s| ≤ sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by
  have hz : (x + y) ^ 2 = z ^ 2 := by linear_combination (x + y - z) * hxyz
  have this :=
    calc
      2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)
        ≤ _ * _ ^ 3 := by gcongr; exact lhs_ineq hxy
      _ ≤ (3 * (x + y) ^ 2 + 2 * s ^ 2) ^ 4 / 4 ^ 4 := mid_ineq
      _ ≤ (2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4 := by
          gcongr (?_ + _) ^ 4 / _
          apply rhs_ineq
  refine le_of_pow_le_pow_left two_ne_zero (by positivity) ?_
  calc
    (32 * |x * y * z * s|) ^ 2 = 32 * (2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)) := by
      rw [mul_pow, sq_abs, hz]; ring
    _ ≤ 32 * ((2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4) := by gcongr
    _ = (sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2) ^ 2 := by
      field_simp
      rw [mul_pow, sq_sqrt zero_le_two, hz]
      ring
#align imo2006_q3.subst_wlog Imo2006Q3.subst_wlog

/-- Proof that `M = 9 * sqrt 2 / 32` works with the substitution. -/
theorem subst_proof₁ (x y z s : ℝ) (hxyz : x + y + z = 0) :
    |x * y * z * s| ≤ sqrt 2 / 32 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by
  wlog h' : 0 ≤ x * y generalizing x y z; swap
  · rw [div_mul_eq_mul_div, le_div_iff' zero_lt_32]
    exact subst_wlog h' hxyz
  cases' (mul_nonneg_of_three x y z).resolve_left h' with h h
  · convert this y z x _ h using 2 <;> linarith
  · convert this z x y _ h using 2 <;> linarith
#align imo2006_q3.subst_proof₁ Imo2006Q3.subst_proof₁

theorem proof₁ {a b c : ℝ} :
    |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
      9 * sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=
  calc
    _ = |(a - b) * (b - c) * (c - a) * -(a + b + c)| := by ring_nf
    _ ≤ _ := subst_proof₁ (a - b) (b - c) (c - a) (-(a + b + c)) (by ring)
    _ = _ := by ring
#align imo2006_q3.proof₁ Imo2006Q3.proof₁

theorem proof₂ (M : ℝ)
    (h : ∀ a b c : ℝ,
      |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
        M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) :
    9 * sqrt 2 / 32 ≤ M := by
  set α := sqrt (2:ℝ)
  have hα : α ^ 2 = 2 := sq_sqrt (by norm_num)
  let a := 2 - 3 * α
  let c := 2 + 3 * α
  calc _ = 18 ^ 2 * 2 * α / 48 ^ 2 := by ring
    _ ≤ M := ?_
  rw [div_le_iff (by positivity)]
  calc 18 ^ 2 * 2 * α
      = 18 ^ 2 * α ^ 2 * α := by linear_combination -324 * α * hα
    _ = abs (-(18 ^ 2 * α ^ 2 * α)) := by rw [abs_neg, abs_of_nonneg]; positivity
    _ = |a * 2 * (a ^ 2 - 2 ^ 2) + 2 * c * (2 ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| := by ring_nf
    _ ≤ M * (a ^ 2 + 2 ^ 2 + c ^ 2) ^ 2 := by apply h
    _ = M * 48 ^ 2 := by linear_combination (324 * α ^ 2 + 1080) * M * hα
#align imo2006_q3.proof₂ Imo2006Q3.proof₂

end Imo2006Q3

open Imo2006Q3

theorem imo2006_q3 (M : ℝ) :
    (∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
          M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ↔
      9 * sqrt 2 / 32 ≤ M :=
  ⟨proof₂ M, fun h _ _ _ => proof₁.trans (by gcongr)⟩
#align imo2006_q3 imo2006_q3
