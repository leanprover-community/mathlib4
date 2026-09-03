/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Lipschitz smoothness in one dimension

For `f : 𝕜 → F`, the Fréchet-derivative formulation of Lipschitz smoothness reduces to the usual
derivative bound

`‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2`.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : 𝕜 → F}

theorem lipschitzSmoothWith_iff_deriv :
    LipschitzSmoothWith 𝕜 K f ↔ Differentiable 𝕜 f ∧
      ∀ x y : 𝕜,
        ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  constructor
  · rintro ⟨hf, hbound⟩
    refine ⟨hf, fun x y ↦ ?_⟩
    simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using hbound x y
  · rintro ⟨hf, hbound⟩
    refine ⟨hf, fun x y ↦ ?_⟩
    simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using hbound x y
