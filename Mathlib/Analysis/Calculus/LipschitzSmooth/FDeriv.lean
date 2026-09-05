/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Quantitative consequences of Lipschitz smoothness

This file develops quantitative consequences of Lipschitz smoothness in terms of the Fréchet
derivative: variation along a chord and, for real-valued functions, the upper and lower quadratic
bounds usually called the descent lemma and, sometimes, the ascent lemma.
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
