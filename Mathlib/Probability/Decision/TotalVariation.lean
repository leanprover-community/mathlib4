/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Decision.StatInfo

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
noncomputable def tv (μ ν : Measure 𝓧) : ℝ := (statInfo μ ν (boolMeasure 1 1)).toReal

instance : IsFiniteMeasure (boolMeasure 1 1) := by constructor; simp

@[simp] lemma tv_zero_left : tv (0 : Measure 𝓧) ν = 0 := by simp [tv]

@[simp] lemma tv_zero_right : tv μ (0 : Measure 𝓧) = 0 := by simp [tv]

@[simp] lemma tv_self : tv μ μ = 0 := by simp [tv]

lemma tv_nonneg : 0 ≤ tv μ ν := ENNReal.toReal_nonneg

lemma tv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tv μ ν ≤ min (μ.real .univ) (ν.real .univ) := by
  rw [Measure.real, Measure.real, ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _)]
  refine ENNReal.toReal_mono ?_ ?_
  · simp
  · have h := statInfo_le_min (μ := μ) (ν := ν) (π := boolMeasure 1 1)
    simpa only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] using h

/-- **Data processing inequality** for the total variation. -/
lemma tv_comp_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    tv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tv μ ν :=
  ENNReal.toReal_mono statInfo_ne_top (statInfo_comp_le _ _ _ _)

lemma tv_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tv μ ν = min (μ.real .univ) (ν.real .univ)
      - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  have h := statInfo_eq_min_sub_iInf_measurableSet μ ν (boolMeasure 1 1)
  simp only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] at h
  rw [tv, h]
  rw [Measure.real, Measure.real, ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le]
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
  · simp

lemma tv_eq_one_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tv μ ν = 1 - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  simp [tv_eq_min_sub_iInf_measurableSet]

end ProbabilityTheory
