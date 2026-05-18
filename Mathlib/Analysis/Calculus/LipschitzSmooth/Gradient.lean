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

* `lipschitzSmoothWith_iff_inner_gradient` — characterisation of `K`-smoothness
  in gradient form under `Differentiable`.
* `LipschitzSmoothWith.inner_gradient_descent_le` — the descent inequality in
  gradient form.
* `LipschitzSmoothWith.inner_gradient_sub_le` — the gradient-variation bound
  `⟪∇ f y - ∇ f x, y - x⟫ ≤ K · ‖y - x‖²`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

/-- Characterisation of `LipschitzSmoothWith` on a Hilbert space in gradient form under
`Differentiable`. -/
theorem lipschitzSmoothWith_iff_inner_gradient (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔
      ∀ x y : F, f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [inner_gradient_left, dist_eq_norm']

namespace LipschitzSmoothWith

/-- For a differentiable `K`-smooth `f` on a Hilbert space, the descent inequality in
gradient form: `f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 · ‖y - x‖²`. -/
theorem inner_gradient_descent_le (h : LipschitzSmoothWith K f) (hf : Differentiable ℝ f)
    (x y : F) : f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 :=
  (lipschitzSmoothWith_iff_inner_gradient hf).mp h x y

/-- For a differentiable `K`-smooth `f` on a Hilbert space, the gradient-variation bound:
`⟪∇ f y - ∇ f x, y - x⟫ ≤ K * ‖y - x‖²`. -/
theorem inner_gradient_sub_le (h : LipschitzSmoothWith K f) (hf : Differentiable ℝ f)
    (x y : F) : ⟪∇ f y - ∇ f x, y - x⟫ ≤ ↑K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← ContinuousLinearMap.sub_apply]
  exact h.fderiv_sub_apply_le hf x y

end LipschitzSmoothWith
