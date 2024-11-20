/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.SetIntegral

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

open scoped Classical MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

variable {μ ν : Measure α}

section integral

lemma integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s ≠ ∞) :
    IntegrableOn (fun x ↦ (μ.rnDeriv ν x).toReal) s ν := by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((setLIntegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

lemma setIntegral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν) s).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_eq_withDensity' := setIntegral_toReal_rnDeriv_eq_withDensity'

lemma setIntegral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν) s).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_eq_withDensity := setIntegral_toReal_rnDeriv_eq_withDensity

lemma setIntegral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s ≠ ∞) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν ≤ (μ s).toReal := by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t ≠ ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    ≤ ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_toReal_rnDeriv hμt
        · exact ae_of_all _ (by simp)
  _ = (withDensity ν (rnDeriv μ ν) t).toReal := setIntegral_toReal_rnDeriv_eq_withDensity' ht_m
  _ ≤ (μ t).toReal := by
        gcongr
        · exact hμt
        · apply withDensity_rnDeriv_le
  _ = (μ s).toReal := by rw [measure_toMeasurable s]

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_le := setIntegral_toReal_rnDeriv_le

lemma setIntegral_toReal_rnDeriv' [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (μ s).toReal := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs, Measure.withDensity_rnDeriv_eq _ _ hμν]

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv' := setIntegral_toReal_rnDeriv'

lemma setIntegral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (μ s).toReal := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s, Measure.withDensity_rnDeriv_eq _ _ hμν]

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv := setIntegral_toReal_rnDeriv

lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = (μ Set.univ).toReal := by
  rw [← setIntegral_univ, setIntegral_toReal_rnDeriv hμν Set.univ]

lemma integral_toReal_rnDeriv' [IsFiniteMeasure μ] [SigmaFinite ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = (μ Set.univ).toReal - (μ.singularPart ν Set.univ).toReal := by
  rw [← ENNReal.toReal_sub_of_le (μ.singularPart_le ν Set.univ) (measure_ne_top _ _),
    ← Measure.sub_apply .univ (Measure.singularPart_le μ ν), Measure.measure_sub_singularPart,
    ← Measure.setIntegral_toReal_rnDeriv_eq_withDensity, setIntegral_univ]

end integral

end Measure

end MeasureTheory
