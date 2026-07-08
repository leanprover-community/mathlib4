/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Convex.FDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# First-order convexity inequality via the gradient

On a Hilbert space `F`, for `f : F → ℝ` convex on `s ⊆ F` and differentiable at `x ∈ s`,
the first-order convexity inequality

`f x + ⟪∇ f x, y - x⟫ ≤ f y`

holds for `y ∈ s`. This is the gradient/inner-product restatement of the Fréchet form
in `Mathlib.Analysis.Convex.FDeriv`, lifted via Riesz representation
(`inner_gradient_left`).

## Main results

* `ConvexOn.add_inner_gradient_le` — the first-order convexity inequality (gradient form).
* `ConvexOn.inner_gradient_sub_nonneg` — gradient monotonicity along the chord.
* `ConvexOn.isMinOn_of_gradient_eq_zero` — the first-order optimality condition.
* `convexOn_iff_add_inner_gradient_le` — iff converse.

Concave duals and strict variants are provided alongside.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : F → ℝ} {s : Set F} {x y : F}

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

namespace ConvexOn

/-- For a convex function `f` differentiable at `x` on a Hilbert space, the first-order
inequality `f x + ⟪∇ f x, y - x⟫ ≤ f y` holds. -/
theorem add_inner_gradient_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f x + ⟪∇ f x, y - x⟫ ≤ f y := by
  rw [inner_gradient_left]
  exact hc.add_fderiv_le hx hy hf

/-- Monotonicity of the gradient along the chord: for convex `f` differentiable at `x`
and `y`, `0 ≤ ⟪∇ f y - ∇ f x, y - x⟫`. -/
theorem inner_gradient_sub_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    0 ≤ ⟪∇ f y - ∇ f x, y - x⟫ := by
  rw [inner_sub_left, inner_gradient_left, inner_gradient_left,
    ← ContinuousLinearMap.sub_apply]
  exact hc.fderiv_sub_nonneg hx hy hfx hfy

/-- A convex function attains its minimum on `s` at any critical point: if `f` is convex on
`s`, Fréchet-differentiable at `x ∈ s`, and `∇ f x = 0`, then `x` minimizes `f` on `s`.
Multi-dimensional gradient analogue of `ConvexOn.isMinOn_of_rightDeriv_eq_zero`. -/
theorem isMinOn_of_gradient_eq_zero (hc : ConvexOn ℝ s f) (hx : x ∈ s)
    (hf : DifferentiableAt ℝ f x) (hg : ∇ f x = 0) :
    IsMinOn f s x := fun _ hy => by
  simpa [hg] using hc.add_inner_gradient_le hx hy hf

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` differentiable at `x` on a Hilbert space, the reverse
first-order inequality `f y ≤ f x + ⟪∇ f x, y - x⟫` holds. -/
theorem le_add_inner_gradient (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ := by
  rw [inner_gradient_left]
  exact hc.le_add_fderiv hx hy hf

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order gradient inequality for strictly convex `f`. -/
theorem add_inner_gradient_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hf : DifferentiableAt ℝ f x) :
    f x + ⟪∇ f x, y - x⟫ < f y := by
  rw [inner_gradient_left]
  exact hc.add_fderiv_lt hx hy hxy hf

end StrictConvexOn

namespace StrictConcaveOn

/-- Strict variant of the reverse first-order gradient inequality for strictly concave `f`. -/
theorem lt_add_inner_gradient (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hf : DifferentiableAt ℝ f x) :
    f y < f x + ⟪∇ f x, y - x⟫ := by
  rw [inner_gradient_left]
  exact hc.lt_add_fderiv hx hy hxy hf

end StrictConcaveOn

/-- A differentiable function on a Hilbert space is convex iff it satisfies the first-order
gradient inequality at every pair of points in `s`. -/
theorem convexOn_iff_add_inner_gradient_le (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∀ y ∈ s, f x + ⟪∇ f x, y - x⟫ ≤ f y := by
  rw [convexOn_iff_add_fderiv_le hs hf]
  refine forall_congr' fun _ => imp_congr_right fun _ => forall_congr' fun _ =>
    imp_congr_right fun _ => ?_
  rw [inner_gradient_left]
