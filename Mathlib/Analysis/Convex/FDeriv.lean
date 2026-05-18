/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Convex.LineDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# First-order convexity inequality via the Fréchet derivative

For `f : E → ℝ` convex on `s ⊆ E` and Fréchet-differentiable at `x ∈ s`, the first-order
convexity inequality

`f x + (fderiv ℝ f x) (y - x) ≤ f y`

holds for `y ∈ s`. This is the Fréchet-derivative restatement of the line-derivative form
in `Mathlib.Analysis.Convex.LineDeriv`, lifted via `DifferentiableAt.lineDeriv_eq_fderiv`.

## Main results

* `ConvexOn.add_fderiv_le` — the first-order convexity inequality (Fréchet form).
* `ConcaveOn.le_add_fderiv` — the concave dual.
* `ConvexOn.fderiv_sub_apply_nonneg` — monotonicity: `0 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y - x)`.
* `StrictConvexOn.add_fderiv_lt` — strict variant.
* `convexOn_iff_add_fderiv_le` — iff converse: differentiability plus the first-order
  inequality everywhere implies `ConvexOn`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E} {x y : E}

namespace ConvexOn

/-- For a convex function `f` Fréchet-differentiable at `x`, the first-order inequality
`f x + (fderiv ℝ f x) (y - x) ≤ f y` holds. -/
theorem add_fderiv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y :=
  hf.lineDeriv_eq_fderiv ▸ hc.add_lineDeriv_le hx hy hf.lineDifferentiableAt

/-- Monotonicity of the Fréchet derivative along the chord: for convex `f` differentiable
at `x` and `y`, `0 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y - x)`. -/
theorem fderiv_sub_apply_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    0 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y - x) := by
  rw [ContinuousLinearMap.sub_apply, ← hfx.lineDeriv_eq_fderiv, ← hfy.lineDeriv_eq_fderiv]
  exact hc.lineDeriv_sub_apply_nonneg hx hy hfx.lineDifferentiableAt hfy.lineDifferentiableAt

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` Fréchet-differentiable at `x`, the reverse first-order
inequality `f y ≤ f x + (fderiv ℝ f x) (y - x)` holds. -/
theorem le_add_fderiv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) :=
  hf.lineDeriv_eq_fderiv ▸ hc.le_add_lineDeriv hx hy hf.lineDifferentiableAt

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order inequality for strictly convex `f`:
when `x ≠ y`, the inequality is strict. -/
theorem add_fderiv_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) < f y :=
  hf.lineDeriv_eq_fderiv ▸ hc.add_lineDeriv_lt hx hy hxy hf.lineDifferentiableAt

end StrictConvexOn

/-- A differentiable function is convex iff it satisfies the first-order inequality
at every pair of points in `s`. -/
theorem convexOn_iff_add_fderiv_le (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ConvexOn ℝ s f ↔
      ∀ x ∈ s, ∀ y ∈ s, f x + fderiv ℝ f x (y - x) ≤ f y := by
  rw [convexOn_iff_add_lineDeriv_le hs fun x hx _ _ => (hf x hx).lineDifferentiableAt]
  refine forall_congr' fun x => imp_congr_right fun hx => forall_congr' fun _ =>
    imp_congr_right fun _ => ?_
  rw [(hf x hx).lineDeriv_eq_fderiv]
