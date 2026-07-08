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

For a `K`-smooth function `f : ℝ → F`, the Taylor bound takes its 1D form

`‖f y - f x - (y - x) • deriv f x‖ ≤ K/2 · (y - x)²`,

lifted from the Fréchet-derivative form in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv` via `fderiv_eq_smul_deriv`.
For real-valued `f` the one-sided bounds take their classical forms

`f y ≤ f x + deriv f x * (y - x) + K/2 · (y - x)²`,
`(deriv f y - deriv f x) * (y - x) ≤ K · (y - x)²`,

with the scalar action spelled as multiplication (`smul_eq_mul` bridges the two).
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : NNReal} {f : ℝ → F}

theorem lipschitzSmoothWith_iff_deriv (hf : Differentiable ℝ f) : LipschitzSmoothWith K f ↔
    ∀ x y : ℝ, ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * (y - x) ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [fderiv_eq_smul_deriv, dist_comm, Real.dist_eq, sq_abs]

namespace LipschitzSmoothWith

theorem deriv_norm_le (h : LipschitzSmoothWith K f) (x y : ℝ) (hf : DifferentiableAt ℝ f x) :
    ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_smul_deriv, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_norm_le x y hf

/-! ### Real-valued functions -/

section Real

variable {f : ℝ → ℝ}

theorem deriv_descent_le (h : LipschitzSmoothWith K f) (x y : ℝ) (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + deriv f x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_le x y hf

theorem deriv_descent_ge (h : LipschitzSmoothWith K f) (x y : ℝ) (hf : DifferentiableAt ℝ f x) :
    f x + deriv f x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_ge x y hf

theorem deriv_sub_mul_le (h : LipschitzSmoothWith K f) (x y : ℝ)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (deriv f y - deriv f x) * (y - x) ≤ K * (y - x) ^ 2 := by
  simpa only [sub_apply, fderiv_eq_deriv_mul, ← sub_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_sub_apply_le x y hfx hfy

end Real

end LipschitzSmoothWith
