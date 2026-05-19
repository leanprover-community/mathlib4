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
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x, y`. This is the conclusion of
the Baillon-Haddad theorem (`K`-smooth + convex ⟹ `K`-cocoercive); this file packages
only the predicate and the elementary direction `K`-cocoercive ⟹ `K`-Lipschitz gradient,
which is a pure Cauchy-Schwarz consequence and needs no convexity or smoothness input.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

open scoped Gradient RealInnerProductSpace

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x, y`. Equivalent to the standard
`(1/K)·‖·‖² ≤ ⟪·,·⟫` form when `0 < K`, but well-defined and meaningful even at `K = 0`
(then forces `∇ f` constant). The conclusion of the Baillon-Haddad theorem. -/
abbrev CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ ↑K * ⟪∇ f y - ∇ f x, y - x⟫

/-- A `K`-cocoercive gradient is `K`-Lipschitz. (One direction of the Baillon-Haddad
characterisation; the reverse requires convexity.) -/
theorem CocoerciveWith.lipschitzWith_gradient {K : NNReal} {f : F → ℝ}
    (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    nlinarith [h x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
              mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]
