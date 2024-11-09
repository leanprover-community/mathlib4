/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# IMO 1963 Q5

Solve the equation `cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1`.

The main idea of the proof is multiply both sides by `2 * sin (π / 7)`, then the result is reached
through basic algebraic manipulations with the use of some trigonometric identities.

-/

open Real

lemma cos_times_sin (x y : ℝ) : 2 * sin x * cos y = (sin (x + y) + sin (x - y)) := by
  simp [sin_add, sin_sub]
  ring

lemma two_sin_pi_over_seven_ne_zero : 2 * sin (π / 7) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, sin_eq_zero_iff, false_or, not_exists]
  intro k
  ring_nf
  by_contra h
  have seven_ne_zero : (7 : ℝ) ≠ 0 := by simp
  rw [mul_comm, mul_right_inj' pi_ne_zero, ← mul_right_inj' seven_ne_zero] at h
  simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.mul_inv_cancel] at h
  norm_cast at h
  apply Int.eq_one_of_mul_eq_one_right (by decide) at h
  contradiction

lemma sin_pi_mul_neg_div (a b : ℝ) : sin (π * (- a / b)) = - sin (π * (a / b)) := by
  ring_nf
  exact sin_neg _

theorem imo1963_q5 : cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2 := by
  rw [← mul_right_inj' two_sin_pi_over_seven_ne_zero, mul_add, mul_sub, ← sin_two_mul,
    cos_times_sin, cos_times_sin]
  ring_nf
  rw [← sin_pi_sub (π * (3 / 7)), sin_pi_mul_neg_div 2 7, sin_pi_mul_neg_div 1 7]
  ring_nf
