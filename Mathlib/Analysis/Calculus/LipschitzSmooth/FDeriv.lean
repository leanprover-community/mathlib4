/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Lipschitz smoothness via the Fréchet derivative

Fréchet-derivative restatements of the `LipschitzSmoothWith` predicate. For differentiable
`f`, `lineDeriv ℝ f x v = fderiv ℝ f x v` pointwise, and the predicate is equivalent to
the two-sided Taylor bound stated in `fderiv` form.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : NNReal} {f : F → ℝ}

theorem lipschitzSmoothWith_iff_fderiv (hf : Differentiable ℝ f) : LipschitzSmoothWith K f ↔
    ∀ x y : F, |f y - f x - fderiv ℝ f x (y - x)| ≤ ↑K / 2 * (dist x y) ^ 2 := by
  rw [lipschitzSmoothWith_iff_lineDeriv]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [(hf x).lineDeriv_eq_fderiv]

namespace LipschitzSmoothWith

theorem fderiv_abs_le (h : LipschitzSmoothWith K f) (x y : F) (hf : DifferentiableAt ℝ f x) :
    |f y - f x - fderiv ℝ f x (y - x)| ≤ ↑K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_abs_le x y

theorem fderiv_descent_le (h : LipschitzSmoothWith K f) (x y : F) (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_le x y

theorem fderiv_descent_ge (h : LipschitzSmoothWith K f) (x y : F) (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) - ↑K / 2 * (dist x y) ^ 2 ≤ f y := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_ge x y

theorem fderiv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_le x y

theorem fderiv_apply_sub_abs_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    |fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x)| ≤ ↑K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_abs_le x y

theorem fderiv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [ContinuousLinearMap.sub_apply]
  exact h.fderiv_apply_sub_le x y hfx hfy

end LipschitzSmoothWith
