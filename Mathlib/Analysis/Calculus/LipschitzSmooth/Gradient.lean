/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness on a Hilbert space via the gradient

On a Hilbert space `F`, the `LipschitzSmoothWith` predicate from
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic` admits a gradient-form
characterisation. For differentiable `f`, `fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫`
via Riesz representation (`inner_gradient_left`), and the descent inequality
becomes `f y ≤ f x + ⟪∇ f x, y - x⟫ + K/2 · ‖y - x‖²`.

This file provides only the characterisation and the elementary variance-bound
consequences; the descent lemma (converse direction) and the Baillon-Haddad
equivalence with cocoercivity are deferred to follow-ups.

## Main results

* `lipschitzSmoothWith_iff_inner_gradient` — characterisation in gradient form under
  `Differentiable`.
* `LipschitzSmoothWith.inner_gradient_descent_le`, `LipschitzSmoothWith.inner_gradient_sub_le` —
  the descent inequality and the variance bound on the gradient.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

theorem lipschitzSmoothWith_iff_inner_gradient (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ ∀ x y : F, f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [inner_gradient_left, dist_eq_norm']

namespace LipschitzSmoothWith

theorem inner_gradient_descent_le (h : LipschitzSmoothWith K f) (x y : F)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_le x y hf

theorem inner_gradient_sub_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    ⟪∇ f y - ∇ f x, y - x⟫ ≤ ↑K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← ContinuousLinearMap.sub_apply]
  exact h.fderiv_sub_apply_le x y hfx hfy

end LipschitzSmoothWith
