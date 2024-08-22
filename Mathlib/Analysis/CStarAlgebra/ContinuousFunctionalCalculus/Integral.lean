/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_integral`: given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ`
  under appropriate conditions

## TODO

+ Prove a similar result for the non-unital case
+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

open MeasureTheory

section unital

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus 𝕜 p]

lemma cfcL_integral (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ) (ha : p a) :
    ∫ x, cfcL ha (f x) ∂μ = cfcL ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcHom_integral (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ) (ha : p a) :
    ∫ x, cfcHom ha (f x) ∂μ = cfcHom ha (∫ x, f x ∂μ) := by
  have h₁ : ∫ x, cfcHom ha (f x) ∂μ = ∫ x, cfcL ha (f x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [cfcHom_eq_cfcL ha]
  rw [h₁, cfcHom_eq_cfcL ha]
  exact cfcL_integral a f hf₁ ha

open ContinuousMap in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x => (spectrum 𝕜 a).restrict (f x)).uncurry)
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_integrable : Integrable bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have ha : p a := ha   -- Needed due to weird autoparam bug
  have hcont : ∀ x, ContinuousOn (f x) (spectrum 𝕜 a) := by
    intro x
    rw [continuousOn_iff_continuous_restrict]
    exact hf.uncurry_left x
  let fc : X → C(spectrum 𝕜 a, 𝕜) := fun x => ⟨_, (hcont x).restrict⟩
  have fc_cont : Continuous fc := by
    refine continuous_of_continuous_uncurry fc ?_
    simp only [coe_mk, restrict_apply, fc]
    exact hf
  have fc_integrable : Integrable fc μ := by
    refine ⟨fc_cont.aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.mono (g := bound) (hbound_integrable.hasFiniteIntegral) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_le _ (norm_nonneg (bound x))]
    intro z
    simp only [coe_mk, restrict_apply, fc]
    exact hbound x z.1 z.2
  have hcont₂ : ContinuousOn (fun r => ∫ x, f x r ∂μ) (spectrum 𝕜 a) := by
    have h₁ : (spectrum 𝕜 a).restrict (fun r => ∫ x, f x r ∂μ) = fun r => (∫ x, fc x ∂μ) r := by
      ext
      simp only [integral_apply fc_integrable, Set.restrict_apply, coe_mk, fc]
    rw [continuousOn_iff_continuous_restrict, h₁]
    exact ContinuousMap.continuous _
  have hrw : (fun x => cfc (f x) a) =ᵐ[μ] fun x => cfcHom ha (fc x) := by
    refine Filter.Eventually.of_forall fun x => ?_
    simp only
    rw [cfc_apply ..]
  rw [integral_congr_ae hrw, cfc_apply .., cfcHom_integral _ _ fc_integrable]
  congr 1
  ext
  simp only [coe_mk, restrict_apply, integral_apply fc_integrable, Set.restrict_apply, coe_mk, fc]

end unital
