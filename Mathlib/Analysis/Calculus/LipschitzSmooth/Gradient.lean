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

On a Hilbert space `F`, the `LipschitzSmoothWith` predicate admits a gradient-form
characterisation. For differentiable `f`, `fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫`
via Riesz representation (`inner_gradient_left`), and the descent inequality becomes
`f y ≤ f x + ⟪∇ f x, y - x⟫ + K/2 · ‖y - x‖²`. The descent lemma (converse direction)
and the Baillon-Haddad equivalence with cocoercivity are deferred to follow-ups.

This file also defines the **`CocoerciveWith K f`** predicate (the conclusion of the
Baillon-Haddad theorem) and the elementary direction `K`-cocoercive ⟹ `K`-Lipschitz
gradient.
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

/-! ### Cocoercivity -/

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x, y`. Equivalent to the standard
`(1/K)·‖·‖² ≤ ⟪·,·⟫` form when `0 < K`, but well-defined and meaningful even at `K = 0`
(then forces `∇ f` constant). The conclusion of the Baillon-Haddad theorem. -/
abbrev CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ ↑K * ⟪∇ f y - ∇ f x, y - x⟫

/-- A `K`-cocoercive gradient is `K`-Lipschitz. (One direction of the Baillon-Haddad
characterisation; the reverse requires convexity.) -/
theorem CocoerciveWith.lipschitzWith_gradient (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    nlinarith [h x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
              mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]
