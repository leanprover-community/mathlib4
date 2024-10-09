/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Exp on the upper half plane

This file contains lemmas about the exponential function on the upper half plane. Useful for
q-expansions of modular forms.
-/

open Real Complex UpperHalfPlane

theorem UpperHalfPlane.abs_exp_two_pi_I_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * π * Complex.I * z))‖ < 1 := by
  simp only [coe_I, Complex.norm_eq_abs, Complex.abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
    ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one,
    sub_self, coe_re, coe_im, zero_sub, exp_lt_one_iff, Left.neg_neg_iff]
  positivity
