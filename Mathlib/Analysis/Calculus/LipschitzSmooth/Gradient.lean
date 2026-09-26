/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness on a Hilbert space via the gradient

On a Hilbert space `F`, Lipschitz smoothness admits a gradient-form characterization. The identity
`fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫` follows from Riesz representation, and the two-sided
Taylor bound becomes

`‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ} {s : Set F}

open scoped Gradient RealInnerProductSpace

theorem lipschitzSmoothWith_iff_inner_gradient :
    LipschitzSmoothWith ℝ K f ↔ Differentiable ℝ f ∧
      ∀ x y : F, ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  constructor <;>
    exact fun ⟨hf, hbound⟩ ↦ ⟨hf, by
      simpa only [inner_gradient_left, dist_eq_norm'] using hbound⟩

/-! ### From a Lipschitz gradient -/

/-- Gradient version of `DifferentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith`. -/
theorem DifferentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith_gradientWithin
    (hf : DifferentiableOn ℝ f s) (hs : Convex ℝ s)
    (hL : LipschitzOnWith K (gradientWithin f s) s) : LipschitzSmoothOnWith ℝ K f s :=
  hf.lipschitzSmoothOnWith_of_lipschitzOnWith hs
    (lipschitzOnWith_fderivWithin_iff_lipschitzOnWith_gradientWithin.mpr hL)

/-- Gradient version of `Differentiable.lipschitzSmoothWith_of_lipschitzWith`. -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith_gradient
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (∇ f)) : LipschitzSmoothWith ℝ K f :=
  hf.lipschitzSmoothWith_of_lipschitzWith
    (lipschitzWith_fderiv_iff_lipschitzWith_gradient.mpr hL)
