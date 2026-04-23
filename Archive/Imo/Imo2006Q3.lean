/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

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

@[expose] public section

open Real

namespace Imo2006Q3

/-- Replacing `x` and `y` with their average increases the left side. -/
theorem lhs_ineq {x y : ℝ} (hxy : 0 ≤ x * y) :
    16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 3 := by
  have : (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y)) ≥ 0 := by positivity
  calc 16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 2 * (x + y) ^ 2 := by gcongr; linarith
    _ = ((x + y) ^ 2) ^ 3 := by ring

theorem four_pow_four_pos : (0 : ℝ) < 4 ^ 4 := by simp

theorem mid_ineq {s t : ℝ} : s * t ^ 3 ≤ (3 * t + s) ^ 4 / 4 ^ 4 := by
  rw [le_div_iff₀ four_pow_four_pos]
  have : 0 ≤ (s - t) ^ 2 * ((s + 7 * t) ^ 2 + 2 * (4 * t) ^ 2) := by positivity
  linarith

/-- Replacing `x` and `y` with their average decreases the right side. -/
theorem rhs_ineq {x y : ℝ} : 3 * (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) := by
  have : 0 ≤ (x - y) ^ 2 := by positivity
  linarith

theorem zero_lt_32 : (0 : ℝ) < 32 := by simp

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
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  calc
    (32 * |x * y * z * s|) ^ 2 = 32 * (2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)) := by
      rw [mul_pow, sq_abs, hz]; ring
    _ ≤ 32 * ((2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4) := by gcongr
    _ = (sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2) ^ 2 := by
      simp [field, hz]
      ring

/-- Proof that `M = 9 * sqrt 2 / 32` works with the substitution. -/
theorem subst_proof₁ (x y z s : ℝ) (hxyz : x + y + z = 0) :
    |x * y * z * s| ≤ sqrt 2 / 32 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by
  wlog h' : 0 ≤ x * y generalizing x y z; swap
  · rw [div_mul_eq_mul_div, le_div_iff₀' zero_lt_32]
    exact subst_wlog h' hxyz
  rcases (mul_nonneg_of_three x y z).resolve_left h' with h | h
  · convert this y z x _ h using 2 <;> linarith
  · convert this z x y _ h using 2 <;> linarith

theorem proof₁ {a b c : ℝ} :
    |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
      9 * sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=
  calc
    _ = |(a - b) * (b - c) * (c - a) * -(a + b + c)| := by ring_nf
    _ ≤ _ := subst_proof₁ (a - b) (b - c) (c - a) (-(a + b + c)) (by ring)
    _ = _ := by ring

theorem proof₂ (M : ℝ)
    (h : ∀ a b c : ℝ,
      |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
        M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) :
    9 * sqrt 2 / 32 ≤ M := by
  set α := sqrt (2 : ℝ)
  have hα : α ^ 2 = 2 := sq_sqrt (by simp)
  let a := 2 - 3 * α
  let c := 2 + 3 * α
  calc _ = 18 ^ 2 * 2 * α / 48 ^ 2 := by ring
    _ ≤ M := ?_
  rw [div_le_iff₀ (by positivity)]
  calc 18 ^ 2 * 2 * α
      = 18 ^ 2 * α ^ 2 * α := by linear_combination -324 * α * hα
    _ = abs (-(18 ^ 2 * α ^ 2 * α)) := by rw [abs_neg, abs_of_nonneg]; positivity
    _ = |a * 2 * (a ^ 2 - 2 ^ 2) + 2 * c * (2 ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| := by ring_nf!
    _ ≤ M * (a ^ 2 + 2 ^ 2 + c ^ 2) ^ 2 := by apply h
    _ = M * 48 ^ 2 := by linear_combination (324 * α ^ 2 + 1080) * M * hα

end Imo2006Q3

open Imo2006Q3

theorem imo2006_q3 (M : ℝ) :
    (∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
          M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ↔
      9 * sqrt 2 / 32 ≤ M :=
  ⟨proof₂ M, fun h _ _ _ => proof₁.trans (by gcongr)⟩
