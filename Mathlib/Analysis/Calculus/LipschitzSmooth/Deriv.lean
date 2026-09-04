/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv
import Mathlib.Analysis.Normed.Operator.Mul

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
  constructor <;>
    exact fun ⟨hf, hbound⟩ ↦ ⟨hf, by
      simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using hbound⟩

/-! ### Lipschitz constants of `fderiv` versus `deriv` -/

section Real

variable {K : NNReal} {f : ℝ → ℝ}

/-- For `f : ℝ → ℝ`, the Lipschitz constants of `fderiv ℝ f` and `deriv f` coincide:
`deriv f` is the composition of `fderiv ℝ f` with the isometry
`(ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm` (evaluation at `1`). -/
theorem lipschitzWith_fderiv_iff_lipschitzWith_deriv :
    LipschitzWith K (fderiv ℝ f) ↔ LipschitzWith K (deriv f) :=
  ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm.isometry.lipschitzWith_iff K).symm

/-! ### Descent lemma -/

/-- **Descent lemma in one dimension.** If `f : ℝ → ℝ` is differentiable and its derivative is
`K`-Lipschitz, then `f` is `K`-smooth. -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith_deriv
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (deriv f)) :
    LipschitzSmoothWith ℝ K f :=
  hf.lipschitzSmoothWith_of_lipschitzWith
    (lipschitzWith_fderiv_iff_lipschitzWith_deriv.mpr hL)

end Real
