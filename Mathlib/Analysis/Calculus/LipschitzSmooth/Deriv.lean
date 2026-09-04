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
variable {K : NNReal} {f : 𝕜 → F} {s : Set 𝕜}

theorem lipschitzSmoothWith_iff_deriv :
    LipschitzSmoothWith 𝕜 K f ↔ Differentiable 𝕜 f ∧
      ∀ x y : 𝕜,
        ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  constructor <;>
    exact fun ⟨hf, hbound⟩ ↦ ⟨hf, by
      simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using hbound⟩

/-! ### Lipschitz constants of `fderiv` versus `deriv` -/

/-- For `f : 𝕜 → F`, the Lipschitz constants of `fderivWithin 𝕜 f s` and `derivWithin f s`
coincide. -/
theorem lipschitzOnWith_fderivWithin_iff_lipschitzOnWith_derivWithin :
    LipschitzOnWith K (fderivWithin 𝕜 f s) s ↔ LipschitzOnWith K (derivWithin f s) s := by
  simp only [lipschitzOnWith_iff_dist_le_mul, ← toSpanSingleton_derivWithin,
    ← ContinuousLinearMap.toSpanSingletonLIE_apply,
    (ContinuousLinearMap.toSpanSingletonLIE 𝕜 F).isometry.dist_eq]

/-- For `f : 𝕜 → F`, the Lipschitz constants of `fderiv 𝕜 f` and `deriv f` coincide:
`deriv f` is the composition of `fderiv 𝕜 f` with the isometry
`(ContinuousLinearMap.toSpanSingletonLIE 𝕜 F).symm` (evaluation at `1`). -/
theorem lipschitzWith_fderiv_iff_lipschitzWith_deriv :
    LipschitzWith K (fderiv 𝕜 f) ↔ LipschitzWith K (deriv f) :=
  ((ContinuousLinearMap.toSpanSingletonLIE 𝕜 F).symm.isometry.lipschitzWith_iff K).symm

/-! ### Descent lemma -/

/-- **Descent lemma in one dimension on a set.** If `f : ℝ → F` is differentiable on a convex
set and its derivative within the set is `K`-Lipschitz there, then `f` is `K`-smooth on the set. -/
theorem DifferentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith_derivWithin
    {f : ℝ → F} {s : Set ℝ} [NormedSpace ℝ F] [CompleteSpace F]
    (hf : DifferentiableOn ℝ f s) (hs : Convex ℝ s)
    (hL : LipschitzOnWith K (derivWithin f s) s) : LipschitzSmoothOnWith ℝ K f s :=
  hf.lipschitzSmoothOnWith_of_lipschitzOnWith hs
    (lipschitzOnWith_fderivWithin_iff_lipschitzOnWith_derivWithin.mpr hL)

/-- **Descent lemma in one dimension.** If `f : ℝ → F` is differentiable and its derivative is
`K`-Lipschitz, then `f` is `K`-smooth. -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith_deriv
    {f : ℝ → F} [NormedSpace ℝ F] [CompleteSpace F]
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (deriv f)) :
    LipschitzSmoothWith ℝ K f :=
  lipschitzSmoothOnWith_univ.mp
    (hf.differentiableOn.lipschitzSmoothOnWith_of_lipschitzOnWith_derivWithin convex_univ
      (by simpa only [derivWithin_univ, lipschitzOnWith_univ] using hL))
