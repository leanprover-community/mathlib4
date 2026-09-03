/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Lipschitz smoothness on a Hilbert space via the gradient

On a Hilbert space `F`, Lipschitz smoothness admits a gradient-form characterisation. The identity
`fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫` follows from Riesz representation, and the two-sided
Taylor bound becomes

`‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

theorem lipschitzSmoothWith_iff_inner_gradient :
    LipschitzSmoothWith ℝ K f ↔
      ∀ x y : F, ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv]
  simp only [inner_gradient_left, dist_eq_norm']

theorem lipschitzSmoothOnWith_iff_inner_gradientWithin {s : Set F}
    (hs : UniqueDiffOn ℝ s) :
    LipschitzSmoothOnWith ℝ K f s ↔ DifferentiableOn ℝ f s ∧
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - ⟪gradientWithin f s x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderivWithin hs]
  simp only [inner_gradientWithin_left, dist_eq_norm']
