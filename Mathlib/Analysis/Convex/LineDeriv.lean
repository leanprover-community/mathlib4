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

## Main results

* `ConvexOn.add_lineDeriv_le` — the first-order convexity inequality (line-derivative
  form).
* `ConcaveOn.le_add_lineDeriv` — the concave dual.
* `ConvexOn.lineDeriv_sub_apply_nonneg` — monotonicity of the directional derivative:
  `0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`.
* `StrictConvexOn.add_lineDeriv_lt` — strict variant under `StrictConvexOn`.
* `convexOn_iff_add_lineDeriv_le` — iff converse: line-differentiability everywhere plus
  the first-order inequality implies `ConvexOn`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {s : Set E} {x y : E}

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function convex on `s`, where `x, y ∈ s`,
is convex on `Icc 0 1` (the segment from `x` to `y` lies in `s` by convexity of `s`). -/
theorem ConvexOn.lineRestriction (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  rw [show (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y from
    funext fun t => by rw [Function.comp_apply, AffineMap.lineMap_apply_module', add_comm]]
  exact (hc.comp_affineMap (AffineMap.lineMap x y)).subset
    (fun t ht => hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht))
    (convex_Icc _ _)

/-- The 1D restriction `t ↦ f (x + t • (y - x))` of a function concave on `s`, where `x, y ∈ s`,
is concave on `Icc 0 1`. -/
theorem ConcaveOn.lineRestriction (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) :
    ConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => f (x + t • (y - x))) := by
  rw [show (fun t : ℝ => f (x + t • (y - x))) = f ∘ AffineMap.lineMap x y from
    funext fun t => by rw [Function.comp_apply, AffineMap.lineMap_apply_module', add_comm]]
  exact (hc.comp_affineMap (AffineMap.lineMap x y)).subset
    (fun t ht => hc.1.segment_subset hx hy (lineMap_mem_segment ℝ x y ht))
    (convex_Icc _ _)

namespace ConvexOn

/-- For a convex function `f` line-differentiable at `x` in direction `y - x`,
the first-order inequality `f x + lineDeriv ℝ f x (y - x) ≤ f y` holds. -/
theorem add_lineDeriv_le (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) ≤ f y := by
  simpa using (hc.lineRestriction hx hy).add_hasDerivAt_mul_le
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf.hasDerivAt

/-- Monotonicity of the directional derivative along the chord: for convex `f`
line-differentiable at both endpoints in direction `y - x`,
`0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)`. -/
theorem lineDeriv_sub_apply_nonneg (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hfx : LineDifferentiableAt ℝ f x (y - x))
    (hfy : LineDifferentiableAt ℝ f y (y - x)) :
    0 ≤ lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) := by
  have h2 := hc.add_lineDeriv_le hy hx (neg_sub y _ ▸ neg_one_smul ℝ (y - x) ▸ hfy.smul _)
  rw [(neg_sub _ _).symm, lineDeriv_neg] at h2
  linarith [hc.add_lineDeriv_le hx hy hfx]

end ConvexOn

namespace ConcaveOn

/-- For a concave function `f` line-differentiable at `x` in direction `y - x`,
the reverse first-order inequality `f y ≤ f x + lineDeriv ℝ f x (y - x)` holds. -/
theorem le_add_lineDeriv (hc : ConcaveOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) := by
  simpa using (hc.lineRestriction hx hy).le_add_hasDerivAt_mul
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one hf.hasDerivAt

end ConcaveOn

namespace StrictConvexOn

/-- Strict variant of the first-order inequality for strictly convex `f`:
when `x ≠ y`, the inequality is strict. -/
theorem add_lineDeriv_lt (hc : StrictConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : LineDifferentiableAt ℝ f x (y - x)) :
    f x + lineDeriv ℝ f x (y - x) < f y := by
  have h₂ : (0 : ℝ) < 1 / 2 := by norm_num
  calc f x + lineDeriv ℝ f x (y - x)
      = 2 * (f x + (1 / 2) * lineDeriv ℝ f x (y - x)) - f x := by ring
    _ ≤ 2 * f (((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • y) - f x := by
        have hm_eq : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • y - x = ((1 : ℝ) / 2) • (y - x) := by
          module
        have h := hc.convexOn.add_lineDeriv_le hx (hc.1 hx hy h₂.le h₂.le (by norm_num))
          (hm_eq.symm ▸ hf.smul _)
        simp only [hm_eq, lineDeriv_smul, smul_eq_mul] at h
        linarith
    _ < 2 * ((1 / 2) * f x + (1 / 2) * f y) - f x := by
        have h := hc.2 hx hy hxy h₂ h₂ (by norm_num)
        simp at h
        linarith
    _ = f y := by ring

end StrictConvexOn

/-- A line-differentiable function is convex iff it satisfies the first-order inequality
at every pair of points in `s`. -/
theorem convexOn_iff_add_lineDeriv_le (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, ∀ y ∈ s, LineDifferentiableAt ℝ f x (y - x)) :
    ConvexOn ℝ s f ↔
      ∀ x ∈ s, ∀ y ∈ s, f x + lineDeriv ℝ f x (y - x) ≤ f y := by
  refine ⟨fun hc x hx y hy => hc.add_lineDeriv_le hx hy (hf x hx y hy), fun H => ⟨hs, ?_⟩⟩
  intro x hx y hy a b ha hb hab
  set z := a • x + b • y with hz
  set L := lineDeriv ℝ f z (x - y)
  change f z ≤ a • f x + b • f y
  simp only [smul_eq_mul]
  calc f z
      = a * (f z + b * L) + b * (f z - a * L) := by linear_combination (f z) * hab.symm
    _ ≤ a * f x + b * f y := by
        have hb_eq : b = 1 - a := by linarith
        have hzs : z ∈ s := hs hx hy ha hb hab
        have hzx : f z + b * L ≤ f x := by
          have hxz : x - z = b • (x - y) := by rw [hz, hb_eq]; module
          simpa only [hxz, lineDeriv_smul, smul_eq_mul] using H z hzs x hx
        have hzy : f z - a * L ≤ f y := by
          have hyz : y - z = -(a • (x - y)) := by rw [hz, hb_eq]; module
          simpa only [hyz, lineDeriv_neg, lineDeriv_smul, smul_eq_mul, ← sub_eq_add_neg]
            using H z hzs y hy
        exact add_le_add (mul_le_mul_of_nonneg_left hzx ha) (mul_le_mul_of_nonneg_left hzy hb)
