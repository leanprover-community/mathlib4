/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from [0, ∞) to [1, ∞).

## Main definitions

- `Real.arcosh`: The inverse function of `Real.cosh`.

## Main Results

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
def arcosh (x : ℝ) :=
  log (x + √(x ^ 2 - 1))

theorem exp_arcosh (x : ℝ) (hx : 1 ≤ x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

/-- `arcosh` is the right inverse of `cosh` over [1, ∞). -/
@[simp]
theorem cosh_arcosh (x : ℝ) (hx : 1 ≤ x) : cosh (arcosh x) = x := by
  unfold arcosh
  have inv : (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two_sub_pow_two, sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx)), sub_sub_cancel]
  rw [cosh_eq, exp_neg, exp_log (by positivity), inv]
  ring

/-- `arcosh` is the left inverse of `cosh` over [0, ∞). -/
@[simp]
theorem arcosh_cosh (x : ℝ) (hx : 0 ≤ x) : arcosh (cosh x) = x := by
  unfold arcosh
  apply exp_eq_exp.mp
  rw [exp_log (by positivity)]
  apply add_eq_of_eq_sub'
  rw [exp_sub_cosh]
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [← sinh_sq, sq_sqrt (by positivity)]

end Real
