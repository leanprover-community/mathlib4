/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Decomposition.SignedLebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

The file also contains properties of `rnDeriv` that use the Radon-Nikodym theorem, notably
* `MeasureTheory.Measure.rnDeriv_withDensity_left`: the Radon-Nikodym derivative of
  `μ.withDensity f` with respect to `ν` is `f * μ.rnDeriv ν`.
* `MeasureTheory.Measure.rnDeriv_withDensity_right`: the Radon-Nikodym derivative of
  `μ` with respect to `ν.withDensity f` is `f⁻¹ * μ.rnDeriv ν`.
* `MeasureTheory.Measure.inv_rnDeriv`: `(μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ`.
* `MeasureTheory.Measure.setLIntegral_rnDeriv`: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` if `μ ≪ ν`.
  There is also a version of this result for the Bochner integral.

## Tags

Radon-Nikodym theorem
-/


noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

variable {μ ν : Measure α}

end Measure

namespace SignedMeasure

open Measure VectorMeasure

theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff, (_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ),
    totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi, rnDeriv_def, integral_sub,
      setIntegral_toReal_rnDeriv h.1 i, setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      erw [VectorMeasure.sub_apply]
      rw [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi]
    all_goals
      rw [← integrableOn_univ]
      refine IntegrableOn.restrict ?_ MeasurableSet.univ
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable (by fun_prop)
      · rw [setLIntegral_univ]
        exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩

end SignedMeasure

section IntegralRNDerivMul

open Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HaveLebesgueDecomposition μ ν]
  [SigmaFinite μ] {f : α → E}

theorem integrable_rnDeriv_smul_iff (hμν : μ ≪ ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable f μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]

theorem withDensityᵥ_rnDeriv_smul (hμν : μ ≪ ν) (hf : Integrable f μ) :
    ν.withDensityᵥ (fun x ↦ (rnDeriv μ ν x).toReal • f x) = μ.withDensityᵥ f := by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf), withDensity_rnDeriv_eq μ ν hμν]

theorem integral_rnDeriv_smul (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · rw [← setIntegral_univ, ← withDensityᵥ_apply ((integrable_rnDeriv_smul_iff hμν).mpr hf) .univ,
      ← setIntegral_univ, ← withDensityᵥ_apply hf .univ, withDensityᵥ_rnDeriv_smul hμν hf]
  · rw [integral_undef hf, integral_undef]
    contrapose! hf
    exact (integrable_rnDeriv_smul_iff hμν).mp hf

lemma setIntegral_rnDeriv_smul (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  simp_rw [← integral_indicator hs, Set.indicator_smul, integral_rnDeriv_smul hμν]

end IntegralRNDerivMul

end MeasureTheory
