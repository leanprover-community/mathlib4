/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Quantitative consequences of Lipschitz smoothness

This file develops the quantitative Fréchet-derivative API for globally and setwise
Lipschitz-smooth functions: variation bounds for the derivative and, for real-valued functions,
the upper and lower quadratic bounds usually called the descent lemma and, sometimes, the ascent
lemma.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

namespace LipschitzSmoothWith

/-- Two-sided bound on the variation of the Fréchet derivative along `y - x`. -/
theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ ≤ K * dist x y ^ 2 := by
  have hyx := h.fderiv_norm_le y x
  rw [← neg_sub y x, map_neg, sub_neg_eq_add, dist_comm] at hyx
  have hsum := (norm_add_le _ _).trans (add_le_add hyx (h.fderiv_norm_le x y))
  rw [show f x - f y + fderiv 𝕜 f y (y - x) +
      (f y - f x - fderiv 𝕜 f x (y - x)) =
        fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x) by abel] at hsum
  linarith

end LipschitzSmoothWith

namespace LipschitzSmoothOnWith

variable {s : Set E}

/-- Two-sided bound on the variation of the within-set Fréchet derivative along `y - x`. -/
theorem fderivWithin_apply_sub_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    (hs : UniqueDiffOn 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖fderivWithin 𝕜 f s y (y - x) - fderivWithin 𝕜 f s x (y - x)‖ ≤
      K * dist x y ^ 2 := by
  have hyx := h.fderivWithin_norm_le hs hy hx
  rw [← neg_sub y x, map_neg, sub_neg_eq_add, dist_comm] at hyx
  have hsum := (norm_add_le _ _).trans (add_le_add hyx (h.fderivWithin_norm_le hs hx hy))
  rw [show f x - f y + fderivWithin 𝕜 f s y (y - x) +
      (f y - f x - fderivWithin 𝕜 f s x (y - x)) =
        fderivWithin 𝕜 f s y (y - x) - fderivWithin 𝕜 f s x (y - x) by abel] at hsum
  linarith

end LipschitzSmoothOnWith

/-! ### Real-valued functions -/

namespace LipschitzSmoothWith

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

/-- The one-sided variation bound in functional form. -/
theorem fderiv_sub_apply_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K * dist x y ^ 2 := by
  rw [sub_apply]
  exact h.fderiv_apply_sub_le x y

end LipschitzSmoothWith

namespace LipschitzSmoothOnWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ} {s : Set E}

/-- The quadratic upper bound on `f y` within a set. -/
theorem fderivWithin_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    f y ≤ f x + fderivWithin ℝ f s x (y - x) + K / 2 * dist x y ^ 2 := by
  linarith [(abs_le.mp (h.fderivWithin_norm_le hs hx hy)).2]

/-- The quadratic lower bound on `f y` within a set. -/
theorem fderivWithin_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    f x + fderivWithin ℝ f s x (y - x) - K / 2 * dist x y ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.fderivWithin_norm_le hs hx hy)).1]

/-- One-sided bound on the variation of the within-set Fréchet derivative along `y - x`. -/
theorem fderivWithin_apply_sub_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    fderivWithin ℝ f s y (y - x) - fderivWithin ℝ f s x (y - x) ≤
      K * dist x y ^ 2 :=
  le_of_abs_le (h.fderivWithin_apply_sub_norm_le hs hx hy)

/-- The one-sided within-set variation bound in functional form. -/
theorem fderivWithin_sub_apply_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (fderivWithin ℝ f s y - fderivWithin ℝ f s x) (y - x) ≤ K * dist x y ^ 2 := by
  rw [sub_apply]
  exact h.fderivWithin_apply_sub_le hs hx hy

end LipschitzSmoothOnWith
