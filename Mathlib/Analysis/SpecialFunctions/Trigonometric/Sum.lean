/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Sum of sines and cosines

This file collects theorems about `∑ i ∈ Finset.range n, sin (a * i + b)` and
`∑ i ∈ Finset.range n, cos (a * i + b)`.
-/

public section

open scoped Real

namespace Complex

theorem sin_mul_sum_sin (n : ℕ) (a b : ℂ) :
    sin (a / 2) * ∑ i ∈ Finset.range n, sin (a * i + b) =
      sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (-2 : ℂ) ≠ 0 by simp)
  simp_rw [← mul_assoc, Finset.mul_sum]
  convert_to ∑ i ∈ Finset.range n,
    -2 * sin (((a * ((i + 1 : ℕ) - 1 / 2) + b) + -(a * (i - 1 / 2) + b)) / 2) *
    sin (((a * ((i + 1 : ℕ) - 1 / 2) + b) - -(a * (i - 1 / 2) + b)) / 2) =
    -2 * sin (n * a / 2) * sin ((n - 1) * a / 2 + b)
  · push_cast
    ring_nf
  simp_rw [← cos_sub_cos, cos_neg]
  rw [Finset.sum_range_sub (fun i ↦ cos (a * (i - 1 / 2) + b)) n, cos_sub_cos]
  ring_nf

theorem sum_sin (n : ℕ) {a : ℂ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℂ) :
    ∑ i ∈ Finset.range n, sin (a * i + b) =
      sin (n * a / 2) * sin ((n - 1) * a / 2 + b) / sin (a / 2) := by
  rw [← sin_mul_sum_sin]
  grind [sin_ne_zero_iff]

theorem sin_mul_sum_cos (n : ℕ) (a b : ℂ) :
    sin (a / 2) * ∑ i ∈ Finset.range n, cos (a * i + b) =
      sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by simp)
  simp_rw [← mul_assoc, Finset.mul_sum]
  convert_to ∑ i ∈ Finset.range n,
    2 * sin (((a * ((i + 1 : ℕ) - 1 / 2) + b) - (a * (i - 1 / 2) + b)) / 2) *
    cos (((a * ((i + 1 : ℕ) - 1 / 2) + b) + (a * (i - 1 / 2) + b)) / 2) =
    2 * sin (n * a / 2) * cos ((n - 1) * a / 2 + b)
  · push_cast
    ring_nf
  simp_rw [← sin_sub_sin]
  rw [Finset.sum_range_sub (fun i ↦ sin (a * (i - 1 / 2) + b)) n, sin_sub_sin]
  ring_nf

theorem sum_cos (n : ℕ) {a : ℂ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℂ) :
    ∑ i ∈ Finset.range n, cos (a * i + b) =
      sin (n * a / 2) * cos ((n - 1) * a / 2 + b) / sin (a / 2) := by
  rw [← sin_mul_sum_cos]
  grind [sin_ne_zero_iff]

end Complex

namespace Real

theorem sin_mul_sum_sin (n : ℕ) (a b : ℝ) :
    sin (a / 2) * ∑ i ∈ Finset.range n, sin (a * i + b) =
      sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_sin n a b).re)

theorem sum_sin (n : ℕ) {a : ℝ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℝ) :
    ∑ i ∈ Finset.range n, sin (a * i + b) =
      sin (n * a / 2) * sin ((n - 1) * a / 2 + b) / sin (a / 2) := by
  have h := Complex.sum_sin n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

theorem sin_mul_sum_cos (n : ℕ) (a b : ℝ) :
    sin (a / 2) * ∑ i ∈ Finset.range n, cos (a * i + b) =
      sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_cos n a b).re)

theorem sum_cos (n : ℕ) {a : ℝ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℝ) :
    ∑ i ∈ Finset.range n, cos (a * i + b) =
      sin (n * a / 2) * cos ((n - 1) * a / 2 + b) / sin (a / 2) := by
  have h := Complex.sum_cos n (a := a) (by exact_mod_cast h) b
  exact_mod_cast congr($(h).re)

end Real
