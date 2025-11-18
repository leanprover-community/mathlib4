/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.Algebra.Module.PointwiseConvergence

/-!
# TemperedDistribution
## Main definitions
* `TemperedDistribution 𝕜 E F V`: The space `𝓢(E, F) →L[𝕜] V` equipped with the pointwise
convergence topology.
* `TemperedDistribution.derivCLM`: The one-dimensional distributional derivative
* `TemperedDistribution.pderivCLM`: Partial distributional derivatives
* `SchwartzMap.toTemperedDistributionCLM`: The canonical embedding of `𝓢(E, F)` into
`𝓢'(𝕜, E, F →L[𝕜] V, V)`.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
tempered distribution.
* `MeasureTheory.Measure.HasTemperateGrowth`: Every measure of temperate growth is a tempered
distribution.
## Main statements
* `derivCLM_toTemperedDistributionCLM_eq`: The equality of the distributional derivative and the
classical derivative.
## Notation
* `𝓢'(𝕜, E, F, V)`: The space of tempered distributions `TemperedDistribution 𝕜 E F V` localized
in `SchwartzSpace`
-/

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' H D E F G V W R : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup D] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedAddCommGroup H] [NormedAddCommGroup V] [NormedAddCommGroup W]

section definition

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable (𝕜 E F V)

abbrev TemperedDistribution := 𝓢(E, F) →Lₚₜ[𝕜] V

scoped[SchwartzMap] notation "𝓢'(" 𝕜 ", " E ", " F ", " V ")" => TemperedDistribution 𝕜 E F V

end definition

namespace TemperedDistribution


section Construction

variable [NormedSpace ℝ E] [NormedSpace ℝ D]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ G] [NormedSpace 𝕜 G]
  [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

variable (V W) in
def mkCLM (A : (𝓢(E, F) →L[𝕜] V) →ₗ[𝕜] (𝓢(D, G) →L[𝕜] W))
  (hbound : ∀ (f : 𝓢(D, G)), ∃ (s : Finset 𝓢(E, F)) (C : ℝ≥0),
  ∀ (B : 𝓢(E, F) →L[𝕜] V), ∃ (g : 𝓢(E, F)) (_hb : g ∈ s),
  ‖(A B) f‖ ≤ C • ‖B g‖) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, D, G, W) where
  __ := (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply Seminorm.continuous_from_bounded PointwiseConvergenceCLM.withSeminorms
      PointwiseConvergenceCLM.withSeminorms
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    obtain ⟨g, h₁, h₂⟩ := h ((toUniformConvergenceCLM _ _ _).symm B)
    refine le_trans ?_ (Seminorm.le_finset_sup_apply h₁)
    exact h₂

variable (V) in
def mkCompCLM (A : 𝓢(D, G) →L[𝕜] 𝓢(E, F)) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, D, G, V) :=
    mkCLM V V
      {toFun f := f ∘L A, map_add' f g := by simp, map_smul' := by simp}
      (by
        intro f
        use {A f}, 1
        simp)

@[simp]
theorem mkCompCLM_apply_apply (A : 𝓢(D, G) →L[𝕜] 𝓢(E, F)) (f : 𝓢'(𝕜, E, F, V)) (g : 𝓢(D, G)) :
    (mkCompCLM V A) f g = f (A g) := rfl

theorem mkCompCLM_comp (A B : 𝓢(E, F) →L[𝕜] 𝓢(E, F)) :
    (mkCompCLM V A) ∘L (mkCompCLM V B) = mkCompCLM V (B ∘L A) := by
  ext f g
  simp only [coe_comp', Function.comp_apply, mkCompCLM_apply_apply]

@[simp]
theorem mkCompCLM_id : (mkCompCLM V (.id 𝕜 𝓢(E, F))) = .id _ _ := by
  ext f g
  simp only [mkCompCLM_apply_apply, coe_id', id_eq]

end Construction

end TemperedDistribution
