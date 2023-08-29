/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

#align_import ring_theory.polynomial.hermite.gaussian from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a gaussian.

## Results

* `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
  The Hermite polynomial is (up to sign) the polynomial factor occurring in the
  `n`th derivative of a gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/


noncomputable section

open Polynomial

namespace Polynomial

/-- `hermite n` is (up to sign) the factor appearing in `deriv^[n]` of a gaussian -/
theorem deriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  rw [mul_assoc]
  -- ⊢ deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x = (-1) ^ n * (↑(aeval x) (her …
  induction' n with n ih generalizing x
  -- ⊢ deriv^[Nat.zero] (fun y => Real.exp (-(y ^ 2 / 2))) x = (-1) ^ Nat.zero * (↑ …
  · rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
    -- 🎉 no goals
  · replace ih : deriv^[n] _ = _ := _root_.funext ih
    -- ⊢ deriv^[Nat.succ n] (fun y => Real.exp (-(y ^ 2 / 2))) x = (-1) ^ Nat.succ n  …
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2 / 2))) x = -x * Real.exp (-(x ^ 2 / 2)) := by
      rw [deriv_exp (by simp)]; simp; ring -- Porting note: was `simp [mul_comm, ← neg_mul]`
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, hermite_succ, map_sub, map_mul, aeval_X, Polynomial.deriv_aeval]
    ring
    -- ⊢ DifferentiableAt ℝ (fun x => ↑(aeval x) (hermite n)) x
    · apply Polynomial.differentiable_aeval
      -- 🎉 no goals
    · apply DifferentiableAt.exp; simp -- Porting note: was just `simp`
      -- ⊢ DifferentiableAt ℝ (fun x => -(x ^ 2 / 2)) x
                                  -- 🎉 no goals
#align polynomial.deriv_gaussian_eq_hermite_mul_gaussian Polynomial.deriv_gaussian_eq_hermite_mul_gaussian

theorem hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / Real.exp (-(x ^ 2 / 2)) := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  -- ⊢ ↑(aeval x) (hermite n) = (-1) ^ n * ((-1) ^ n * ↑(aeval x) (hermite n) * Rea …
  field_simp [Real.exp_ne_zero]
  -- ⊢ ↑(aeval x) (hermite n) * Real.exp (-x ^ 2 / 2) = (-1) ^ n * ((-1) ^ n * ↑(ae …
  rw [← @smul_eq_mul ℝ _ ((-1) ^ n), ← inv_smul_eq_iff₀, mul_assoc, smul_eq_mul, ← inv_pow, ←
    neg_inv, inv_one]
  exact pow_ne_zero _ (by norm_num)
  -- 🎉 no goals
#align polynomial.hermite_eq_deriv_gaussian Polynomial.hermite_eq_deriv_gaussian

theorem hermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  rw [hermite_eq_deriv_gaussian, Real.exp_neg]
  -- ⊢ (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / (Real.exp (x ^ 2 …
  field_simp [Real.exp_ne_zero]
  -- 🎉 no goals
#align polynomial.hermite_eq_deriv_gaussian' Polynomial.hermite_eq_deriv_gaussian'

end Polynomial
