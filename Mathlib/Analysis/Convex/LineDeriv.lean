/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# First-order convexity inequality via the directional derivative

For `f : E → ℝ` convex on `s ⊆ E` and line-differentiable at `x ∈ s` in the direction
`y - x`, the first-order convexity inequality

`f x + lineDeriv ℝ f x (y - x) ≤ f y`

holds for `y ∈ s`. This is the directional-derivative form of the convex subgradient
inequality, lifted from the 1D case in `Mathlib.Analysis.Convex.Deriv` by restricting
to the line segment between `x` and `y`.

The `HasLineDerivAt`-flavoured statements are the primitives; the `lineDeriv`-flavoured
ones are corollaries under `LineDifferentiableAt`.

## Main results

* `ConvexOn.add_lineDeriv_le` — the first-order convexity inequality
  (line-derivative form).
* `ConvexOn.lineDeriv_sub_nonneg` — monotonicity of the directional derivative along the
  chord.

Concave duals and strict variants are provided alongside.

The iff converse to the first-order inequality lives at the Fréchet layer
(`convexOn_iff_add_fderiv_le` in `Mathlib.Analysis.Convex.FDeriv`); the LineDeriv layer
contains only forward implications.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E} {x y : E}

private theorem lineMap_eq_add_smul_sub (x y : E) (t : ℝ) :
    AffineMap.lineMap x y t = x + t • (y - x) := by
  rw [AffineMap.lineMap_apply_module']; abel

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function convex on `s`, where `x, y ∈ s`,
is convex on `Icc 0 1` (the segment from `x` to `y` lies in `s` by convexity of `s`). -/
theorem ConvexOn.lineRestriction (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  rw [show (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y from
    funext fun t => by rw [Function.comp_apply, lineMap_eq_add_smul_sub]]
  exact (hc.comp_affineMap (AffineMap.lineMap x y)).subset
    (fun t ht => hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht))
    (convex_Icc _ _)

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function concave on `s`, where `x, y ∈ s`,
is concave on `Icc 0 1`. -/
theorem ConcaveOn.lineRestriction (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  rw [show (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y from
    funext fun t => by rw [Function.comp_apply, lineMap_eq_add_smul_sub]]
  exact (hc.comp_affineMap (AffineMap.lineMap x y)).subset
    (fun t ht => hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht))
    (convex_Icc _ _)

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function strictly convex on `s`, with
`x ≠ y` both in `s`, is strictly convex on `Icc 0 1`. -/
theorem StrictConvexOn.lineRestriction (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) :
    StrictConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  refine ⟨convex_Icc _ _, fun t₁ ht₁ t₂ ht₂ ht_ne a b ha hb hab => ?_⟩
  have hsub : (y - x : E) ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hp_ne : x + t₁ • (y - x) ≠ x + t₂ • (y - x) := fun h =>
    ht_ne (smul_left_injective ℝ hsub (add_left_cancel h))
  have hp₁ : x + t₁ • (y - x) ∈ s := by
    rw [← lineMap_eq_add_smul_sub]
    exact hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht₁)
  have hp₂ : x + t₂ • (y - x) ∈ s := by
    rw [← lineMap_eq_add_smul_sub]
    exact hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht₂)
  have hb_eq : b = 1 - a := by linarith
  have hcomb : a • (x + t₁ • (y - x)) + b • (x + t₂ • (y - x))
      = x + (a • t₁ + b • t₂) • (y - x) := by
    rw [hb_eq]; module
  have key := hc.2 hp₁ hp₂ hp_ne ha hb hab
  rw [hcomb] at key
  exact key

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function strictly concave on `s`, with
`x ≠ y` both in `s`, is strictly concave on `Icc 0 1`. -/
theorem StrictConcaveOn.lineRestriction (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  have hneg : StrictConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => -f (x + t • (y - x))) := by
    simpa using hc.neg.lineRestriction hx hy hxy
  simpa [Pi.neg_def] using hneg.neg

namespace ConvexOn

/-- For a convex function `f` with line derivative `f'` at `x` in direction `y - x`,
the first-order inequality `f x + f' ≤ f y` holds. -/
theorem add_hasLineDerivAt_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    {f' : ℝ} (hf : HasLineDerivAt ℝ f f' x (y - x)) :
    f x + f' ≤ f y := by
  simpa using (hc.lineRestriction hx hy).add_hasDerivAt_mul_le
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf

/-- For a convex function `f` line-differentiable at `x` in direction `y - x`,
the first-order inequality `f x + lineDeriv ℝ f x (y - x) ≤ f y` holds. -/
theorem add_lineDeriv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) ≤ f y :=
  hc.add_hasLineDerivAt_le hx hy hf.hasLineDerivAt

/-- Monotonicity of the directional derivative along the chord: for convex `f`
line-differentiable at both endpoints in direction `y - x`,
`0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`. -/
theorem lineDeriv_sub_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : LineDifferentiableAt ℝ f x (y - x))
    (hfy : LineDifferentiableAt ℝ f y (y - x)) :
    0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) := by
  have hfy' : LineDifferentiableAt ℝ f y (x - y) := by
    have := hfy.smul (-1 : ℝ)
    rwa [neg_one_smul, neg_sub] at this
  have h₂ := hc.add_lineDeriv_le hy hx hfy'
  rw [← neg_sub y x, lineDeriv_neg] at h₂
  linarith [hc.add_lineDeriv_le hx hy hfx]

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` with line derivative `f'` at `x` in direction `y - x`,
the reverse first-order inequality `f y ≤ f x + f'` holds. -/
theorem le_add_hasLineDerivAt (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    {f' : ℝ} (hf : HasLineDerivAt ℝ f f' x (y - x)) :
    f y ≤ f x + f' := by
  simpa using (hc.lineRestriction hx hy).le_add_hasDerivAt_mul
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf

/-- For a concave function `f` line-differentiable at `x` in direction `y - x`,
the reverse first-order inequality `f y ≤ f x + lineDeriv ℝ f x (y - x)` holds. -/
theorem le_add_lineDeriv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) :=
  hc.le_add_hasLineDerivAt hx hy hf.hasLineDerivAt

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order inequality for strictly convex `f` with line derivative
`f'` at `x` in direction `y - x`, assuming `x ≠ y`: `f x + f' < f y`. -/
theorem add_hasLineDerivAt_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {f' : ℝ} (hf : HasLineDerivAt ℝ f f' x (y - x)) :
    f x + f' < f y := by
  simpa using (hc.lineRestriction hx hy hxy).add_hasDerivAt_mul_lt
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf

/-- Strict variant of the first-order inequality for strictly convex `f`: when `x ≠ y` and `f`
is line-differentiable at `x` in direction `y - x`, the inequality is strict. -/
theorem add_lineDeriv_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) < f y :=
  hc.add_hasLineDerivAt_lt hx hy hxy hf.hasLineDerivAt

end StrictConvexOn

namespace StrictConcaveOn

/-- Strict variant of the reverse first-order inequality for strictly concave `f` with line
derivative `f'` at `x` in direction `y - x`, assuming `x ≠ y`: `f y < f x + f'`. -/
theorem lt_add_hasLineDerivAt (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {f' : ℝ} (hf : HasLineDerivAt ℝ f f' x (y - x)) :
    f y < f x + f' := by
  simpa using (hc.lineRestriction hx hy hxy).lt_add_hasDerivAt_mul
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf

/-- Strict variant of the reverse first-order inequality for strictly concave `f`: when `x ≠ y`
and `f` is line-differentiable at `x` in direction `y - x`, the inequality is strict. -/
theorem lt_add_lineDeriv (hc : StrictConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f y < f x + lineDeriv ℝ f x (y - x) :=
  hc.lt_add_hasLineDerivAt hx hy hxy hf.hasLineDerivAt

end StrictConcaveOn
