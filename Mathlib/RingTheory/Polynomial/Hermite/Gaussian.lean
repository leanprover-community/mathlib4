/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/
module

public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a Gaussian.

## Results

* `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
  The Hermite polynomial is (up to sign) the polynomial factor occurring in the
  `n`th derivative of a Gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

public section


noncomputable section

open Polynomial

namespace Polynomial

/-- `hermite n` is (up to sign) the factor appearing in `deriv^[n]` of a Gaussian. -/
theorem deriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  rw [mul_assoc]
  induction n generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2 / 2))) x = -x * Real.exp (-(x ^ 2 / 2)) := by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [mul_comm, ← neg_mul]`
      rw [deriv_exp (by simp)]
      simp [mul_comm]
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, hermite_succ, map_sub, map_mul, aeval_X, Polynomial.deriv_aeval]
    · ring
    · apply Polynomial.differentiable_aeval
    · apply DifferentiableAt.exp; simp -- Porting note: was just `simp`

theorem hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / Real.exp (-(x ^ 2 / 2)) := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  field_simp
  rw [← pow_mul]
  simp

theorem hermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  rw [hermite_eq_deriv_gaussian, Real.exp_neg]
  field

end Polynomial
