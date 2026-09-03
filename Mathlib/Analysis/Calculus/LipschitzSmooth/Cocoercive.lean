/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Cocoercivity

A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x`, `y`. This is the conclusion of
the Baillon-Haddad theorem. This file packages only the predicate and the elementary implication
from `K`-cocoercivity to a `K`-Lipschitz gradient.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x`, `y`. This is equivalent to the
standard `(1 / K) · ‖·‖² ≤ ⟪·, ·⟫` form when `0 < K`, but remains meaningful at `K = 0`.
This is the conclusion of the Baillon-Haddad theorem. -/
def CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫

theorem cocoerciveWith_iff :
    CocoerciveWith K f ↔
      ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫ :=
  Iff.rfl

namespace CocoerciveWith

/-- The defining cocoercivity bound. -/
theorem norm_sq_le (h : CocoerciveWith K f) (x y : F) :
    ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫ :=
  h x y

/-- A `K`-cocoercive gradient is `K`-Lipschitz. The reverse implication requires convexity. -/
theorem lipschitzWith_gradient (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    nlinarith [h.norm_sq_le x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
      mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]

end CocoerciveWith
