/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness in 1D via the derivative

For a `K`-smooth function `f : ℝ → ℝ`, the descent inequality and the variation bound
take their classical 1D forms

`f y ≤ f x + deriv f x * (y - x) + K/2 * (y - x)²`,
`(deriv f y - deriv f x) * (y - x) ≤ K * (y - x)²`.

These are 1D restatements of the Fréchet-derivative forms in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`, lifted via `fderiv_eq_deriv_mul`.
-/

public section

variable {K : NNReal} {f : ℝ → ℝ}

theorem lipschitzSmoothWith_iff_deriv (hf : Differentiable ℝ f) : LipschitzSmoothWith K f ↔
    ∀ x y : ℝ, f y ≤ f x + deriv f x * (y - x) + ↑K / 2 * (y - x) ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [fderiv_eq_deriv_mul, dist_comm, Real.dist_eq, sq_abs]

namespace LipschitzSmoothWith

theorem deriv_descent_le (h : LipschitzSmoothWith K f) (x y : ℝ) (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + deriv f x * (y - x) + ↑K / 2 * (y - x) ^ 2 := by
  have := h.fderiv_descent_le x y hf
  rwa [fderiv_eq_deriv_mul, dist_comm, Real.dist_eq, sq_abs] at this

theorem deriv_sub_mul_le (h : LipschitzSmoothWith K f) (x y : ℝ)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (deriv f y - deriv f x) * (y - x) ≤ ↑K * (y - x) ^ 2 := by
  have := h.fderiv_sub_apply_le x y hfx hfy
  rwa [ContinuousLinearMap.sub_apply, fderiv_eq_deriv_mul, fderiv_eq_deriv_mul, ← sub_mul,
    dist_comm, Real.dist_eq, sq_abs] at this

end LipschitzSmoothWith
