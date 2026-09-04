/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Quantitative consequences of Lipschitz smoothness

This file develops quantitative consequences of Lipschitz smoothness in terms of the Fréchet
derivative: variation along a chord and, for real-valued functions, the upper and lower quadratic
bounds usually called the descent lemma and, sometimes, the ascent lemma. It also proves that a
differentiable function with Lipschitz Fréchet derivative is Lipschitz smooth, globally or on a
convex set.
-/

public section

namespace LipschitzSmoothWith

section NormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

/-- Two-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ ≤ K * dist x y ^ 2 := by
  calc
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ =
        ‖(f x - f y - fderiv 𝕜 f y (x - y)) +
          (f y - f x - fderiv 𝕜 f x (y - x))‖ := by
      rw [← neg_sub y x, map_neg]
      congr 1
      abel
    _ ≤ ‖f x - f y - fderiv 𝕜 f y (x - y)‖ +
        ‖f y - f x - fderiv 𝕜 f x (y - x)‖ := norm_add_le _ _
    _ ≤ K / 2 * dist y x ^ 2 + K / 2 * dist x y ^ 2 :=
      add_le_add (h.fderiv_norm_le y x) (h.fderiv_norm_le x y)
    _ = K * dist x y ^ 2 := by rw [dist_comm y x]; ring

end NormedField

/-! ### Real-valued functions -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem fderiv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * dist x y ^ 2 := by
  linarith [(abs_le.mp (h.fderiv_norm_le x y)).2]

/-- The quadratic lower bound on `f y`, sometimes referred to as the *ascent lemma*. -/
theorem fderiv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f x + fderiv ℝ f x (y - x) - K / 2 * dist x y ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.fderiv_norm_le x y)).1]

/-- One-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K * dist x y ^ 2 :=
  le_of_abs_le (h.fderiv_apply_sub_norm_le x y)

end Real

end LipschitzSmoothWith

/-! ### Descent lemma -/

open AffineMap MeasureTheory

open scoped Convex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : NNReal} {f : E → F} {s : Set E}

/-- **Descent lemma on a set.** If `f` is differentiable on a convex set and its Fréchet derivative
within the set is `K`-Lipschitz there, then `f` is `K`-smooth on the set. -/
theorem DifferentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith [CompleteSpace F]
    (hf : DifferentiableOn ℝ f s) (hs : Convex ℝ s)
    (hL : LipschitzOnWith K (fderivWithin ℝ f s) s) : LipschitzSmoothOnWith ℝ K f s := by
  refine ⟨hf, fun x hx y hy ↦ ?_⟩
  have hseg : [x -[ℝ] y] ⊆ s := hs.segment_subset hx hy
  have hLseg := hL.mono hseg
  have h_curve : CurveIntegrable (fderivWithin ℝ f s) (.segment x y) :=
    hLseg.continuousOn.curveIntegrable_segment
  have h_const := curveIntegrable_segment_const (fderivWithin ℝ f s x) x y
  have h_integrable := curveIntegrable_segment.mp (h_curve.sub h_const)
  rw [← curveIntegral_fderivWithin_segment hseg (fun z hz ↦ hf z (hseg hz)) hLseg.continuousOn,
    ← curveIntegral_segment_const, ← curveIntegral_fun_sub h_curve h_const,
    curveIntegral_segment]
  calc
    ‖∫ t in (0 : ℝ)..1,
        (fderivWithin ℝ f s (lineMap x y t) - fderivWithin ℝ f s x) (y - x)‖ ≤
        ∫ t in (0 : ℝ)..1,
          ‖(fderivWithin ℝ f s (lineMap x y t) - fderivWithin ℝ f s x) (y - x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, K * dist x y ^ 2 * t :=
      intervalIntegral.integral_mono_on zero_le_one h_integrable.norm
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht ↦ by
          calc
            ‖(fderivWithin ℝ f s (lineMap x y t) - fderivWithin ℝ f s x) (y - x)‖ ≤
                ‖fderivWithin ℝ f s (lineMap x y t) - fderivWithin ℝ f s x‖ * ‖y - x‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ = dist (fderivWithin ℝ f s x) (fderivWithin ℝ f s (lineMap x y t)) *
                dist x y := by simp only [← dist_eq_norm']
            _ ≤ K * dist x (lineMap x y t) * dist x y :=
              mul_le_mul_of_nonneg_right
                (hL.dist_le_mul x hx _ (hs.lineMap_mem hx hy ht)) dist_nonneg
            _ = K * dist x y ^ 2 * t := by
              rw [dist_left_lineMap, Real.norm_of_nonneg ht.1]
              ring
    _ = K * dist x y ^ 2 * ∫ t in (0 : ℝ)..1, t :=
      intervalIntegral.integral_const_mul _ _
    _ = K / 2 * dist x y ^ 2 := by rw [integral_id]; ring

/-- **Descent lemma.** If `f` is differentiable and its Fréchet derivative is
`K`-Lipschitz, then `f` is `K`-smooth (without convexity assumption). -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith [CompleteSpace F]
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (fderiv ℝ f)) :
    LipschitzSmoothWith ℝ K f :=
  lipschitzSmoothOnWith_univ.mp
    (hf.differentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith convex_univ
      (by simpa only [fderivWithin_univ, lipschitzOnWith_univ] using hL))
