/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Cotangent

This file contains lemmas about the cotangent function. Specifically, useful series expansions.
-/

open Real Complex BigOperators Filter

open scoped UpperHalfPlane Topology

lemma cot_eq_exp_ratio (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  field_simp
  have h1 : exp (z * I) + exp (-(z * I)) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [mul_one, add_left_inj]
    ring_nf
  have h2 : (exp (-(z * I)) - exp (z * I)) * I = exp (-(z * I)) * (I * (1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-The version one probably wants to use more. -/
lemma cot_pi_eq_exp_ratio (z : ℂ) :
    cot (π * z) = (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) := by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

theorem UpperHalfPlane.exp_two_pi_I_lt_one (z : ℍ) :
    Complex.abs (Complex.exp (2 * π * I * z)) < 1 := by
  simp only [coe_I, Complex.abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
    sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re,
    coe_im, zero_sub, exp_lt_one_iff, Left.neg_neg_iff]
  positivity

/-This is the version one probably wants, which is why the pi's are there. -/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n := by
  rw [cot_pi_eq_exp_ratio]
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [h1, one_div,
    (tsum_geometric_of_norm_lt_one (by exact UpperHalfPlane.exp_two_pi_I_lt_one z)).symm ,add_comm]
  rw [geom_series_mul_one_add (Complex.exp (2 * π * I * (z : ℂ)))
    (UpperHalfPlane.exp_two_pi_I_lt_one _) ]
  ring
