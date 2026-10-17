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
in `Mathlib.Analysis.Convex.LineDeriv`, lifted via `HasFDerivAt.hasLineDerivAt`.

The `HasFDerivAt`-flavoured statements are the primitives; the `fderiv`-flavoured ones are
corollaries under `DifferentiableAt`.

## Main results

* `ConvexOn.add_fderiv_le` — the first-order convexity inequality (Fréchet form).
* `ConvexOn.fderiv_sub_nonneg` — monotonicity along the chord.
* `ConvexOn.isMinOn_of_fderiv_eq_zero` — the first-order optimality condition.
* `convexOn_iff_add_fderiv_le` — iff converse: differentiability plus the first-order
  inequality everywhere implies `ConvexOn`.

Concave duals and strict variants are provided alongside.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E} {x y : E}

namespace ConvexOn

/-- For a convex function `f` with Fréchet derivative `f'` at `x`, the first-order inequality
`f x + f' (y - x) ≤ f y` holds. -/
theorem add_hasFDerivAt_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) :
    f x + f' (y - x) ≤ f y :=
  hc.add_hasLineDerivAt_le hx hy (hf.hasLineDerivAt _)

/-- For a convex function `f` Fréchet-differentiable at `x`, the first-order inequality
`f x + (fderiv ℝ f x) (y - x) ≤ f y` holds. -/
theorem add_fderiv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y :=
  hc.add_hasFDerivAt_le hx hy hf.hasFDerivAt

/-- Monotonicity of the Fréchet derivative along the chord: for convex `f` differentiable
at `x` and `y`, `0 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y - x)`. -/
theorem fderiv_sub_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    0 ≤ (fderiv ℝ f y - fderiv ℝ f x) (y - x) := by
  rw [sub_apply, ← hfx.lineDeriv_eq_fderiv, ← hfy.lineDeriv_eq_fderiv]
  exact hc.lineDeriv_sub_nonneg hx hy hfx.lineDifferentiableAt hfy.lineDifferentiableAt

/-- A convex function with a vanishing Fréchet derivative at an interior point of differentiability
attains its minimum there. -/
theorem isMinOn_of_fderiv_eq_zero (hc : ConvexOn ℝ s f) (hx : x ∈ s)
    (hf : DifferentiableAt ℝ f x) (hgrad : fderiv ℝ f x = 0) :
    IsMinOn f s x :=
  fun y hy => by simpa [hgrad] using hc.add_fderiv_le hx hy hf

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` with Fréchet derivative `f'` at `x`, the reverse first-order
inequality `f y ≤ f x + f' (y - x)` holds. -/
theorem le_add_hasFDerivAt (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) :
    f y ≤ f x + f' (y - x) :=
  hc.le_add_hasLineDerivAt hx hy (hf.hasLineDerivAt _)

/-- For a concave function `f` Fréchet-differentiable at `x`, the reverse first-order
inequality `f y ≤ f x + (fderiv ℝ f x) (y - x)` holds. -/
theorem le_add_fderiv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) :=
  hc.le_add_hasFDerivAt hx hy hf.hasFDerivAt

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order inequality for strictly convex `f` with Fréchet derivative
`f'` at `x`, assuming `x ≠ y`: `f x + f' (y - x) < f y`. -/
theorem add_hasFDerivAt_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) :
    f x + f' (y - x) < f y :=
  hc.add_hasLineDerivAt_lt hx hy hxy (hf.hasLineDerivAt _)

/-- Strict variant of the first-order inequality for strictly convex `f`:
when `x ≠ y`, the inequality is strict. -/
theorem add_fderiv_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) < f y :=
  hc.add_hasFDerivAt_lt hx hy hxy hf.hasFDerivAt

end StrictConvexOn

namespace StrictConcaveOn

/-- Strict variant of the reverse first-order inequality for strictly concave `f` with Fréchet
derivative `f'` at `x`, assuming `x ≠ y`: `f y < f x + f' (y - x)`. -/
theorem lt_add_hasFDerivAt (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) :
    f y < f x + f' (y - x) :=
  hc.lt_add_hasLineDerivAt hx hy hxy (hf.hasLineDerivAt _)

/-- Strict variant of the reverse first-order inequality for strictly concave `f`: when `x ≠ y`,
the inequality is strict. -/
theorem lt_add_fderiv (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : DifferentiableAt ℝ f x) :
    f y < f x + fderiv ℝ f x (y - x) :=
  hc.lt_add_hasFDerivAt hx hy hxy hf.hasFDerivAt

end StrictConcaveOn

/-- A differentiable function is convex iff it satisfies the first-order inequality
at every pair of points in `s`. -/
theorem convexOn_iff_add_fderiv_le (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ConvexOn ℝ s f ↔
      ∀ x ∈ s, ∀ y ∈ s, f x + fderiv ℝ f x (y - x) ≤ f y := by
  refine ⟨fun hc x hx y hy => hc.add_fderiv_le hx hy (hf x hx), fun H => ⟨hs, ?_⟩⟩
  intro x hx y hy a b ha hb hab
  set z := a • x + b • y with hz
  set L := fderiv ℝ f z (x - y)
  have hzs : z ∈ s := hs hx hy ha hb hab
  have hb_eq : b = 1 - a := by linarith
  have hzx : f z + b * L ≤ f x := by
    simpa only [show x - z = b • (x - y) by rw [hz, hb_eq]; module, map_smul, smul_eq_mul]
      using H z hzs x hx
  have hzy : f z - a * L ≤ f y := by
    simpa only [show y - z = -(a • (x - y)) by rw [hz, hb_eq]; module, map_neg, map_smul,
      smul_eq_mul, ← sub_eq_add_neg] using H z hzs y hy
  calc f z
      = a * (f z + b * L) + b * (f z - a * L) := by linear_combination (f z) * hab.symm
    _ ≤ a * f x + b * f y :=
        add_le_add (mul_le_mul_of_nonneg_left hzx ha) (mul_le_mul_of_nonneg_left hzy hb)
