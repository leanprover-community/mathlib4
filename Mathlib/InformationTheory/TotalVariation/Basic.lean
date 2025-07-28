/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Decision.DeGrootInfo

/-!
# Total variation distance

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Bool

open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧}

/-- Total variation distance between two measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) : ℝ := (deGrootInfo μ ν (boolMeasure 1 1)).toReal

instance : IsFiniteMeasure (boolMeasure 1 1) := by constructor; simp

@[simp] lemma tvDist_zero_left : tvDist (0 : Measure 𝓧) ν = 0 := by simp [tvDist]

@[simp] lemma tvDist_zero_right : tvDist μ (0 : Measure 𝓧) = 0 := by simp [tvDist]

@[simp] lemma tvDist_self : tvDist μ μ = 0 := by simp [tvDist]

lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma tvDist_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν ≤ min (μ.real .univ) (ν.real .univ) := by
  rw [Measure.real, Measure.real, ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _)]
  refine ENNReal.toReal_mono ?_ ?_
  · simp
  · have h := deGrootInfo_le_min (μ := μ) (ν := ν) (π := boolMeasure 1 1)
    simpa only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] using h

/-- **Data processing inequality** for the total variation distance. -/
lemma tvDist_comp_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν :=
  ENNReal.toReal_mono deGrootInfo_ne_top (deGrootInfo_comp_le _ _ _ _)

lemma tvDist_eq_min_sub_lintegral {ζ : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = min (μ.real .univ) (ν.real .univ)
      - (∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ).toReal := by
  have h := deGrootInfo_eq_min_sub_lintegral' (boolMeasure 1 1) hμζ hνζ
  simp only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] at h
  rw [tvDist, h, Measure.real, Measure.real,
    ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le _ (by simp)]
  calc ∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ
  _ ≤ min (∫⁻ x, (∂μ/∂ζ) x ∂ζ) (∫⁻ x, (∂ν/∂ζ) x ∂ζ) := by
    refine le_min ?_ ?_
    · exact lintegral_mono fun _ ↦ min_le_left _ _
    · exact lintegral_mono fun _ ↦ min_le_right _ _
  _ = min (μ .univ) (ν .univ) := by
    rw [Measure.lintegral_rnDeriv hμζ, Measure.lintegral_rnDeriv hνζ]

lemma tvDist_eq_one_sub_lintegral {ζ : Measure 𝓧} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = 1 - (∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ).toReal := by
  simp [tvDist_eq_min_sub_lintegral hμζ hνζ]

lemma tvDist_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν = min (μ.real .univ) (ν.real .univ)
      - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  have h := deGrootInfo_eq_min_sub_iInf_measurableSet μ ν (boolMeasure 1 1)
  simp only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] at h
  rw [tvDist, h, Measure.real, Measure.real,
    ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le _ (by simp)]
  · congr
    rw [iInf_subtype']
    rw [← ENNReal.toReal_ofReal (r := ⨅ (E : {E //  MeasurableSet E}), μ.real E + ν.real E.1ᶜ)]
    swap; · exact le_ciInf fun E ↦ by positivity
    simp_rw [ENNReal.ofReal_iInf]
    congr with E
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  · simp only [le_inf_iff]
    constructor
    · exact (iInf_le _ .univ).trans (by simp)
    · exact (iInf_le _ ∅).trans (by simp)

lemma tvDist_eq_one_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν = 1 - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  simp [tvDist_eq_min_sub_iInf_measurableSet]

end ProbabilityTheory
