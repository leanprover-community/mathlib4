/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Total variation distance between finite measures

## Main definitions

* `vecTVDist μ ν`: total variation distance between two vector measures, defined as the value on
  the universal set of the variation of `μ - ν`.
* `tvDist μ ν`: total variation distance, defined as the value on the universal set of
  the variation of `μ - ν`, in which both measures are seen as signed measures.

## Main statements

* `fooBar_unique`

## Implementation details



-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two vector measures. -/
noncomputable def vecTVDist {M : Type*} [NormedAddCommGroup M]
    (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

/-- Total variation distance between two finite measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (vecTVDist μ.toSignedMeasure ν.toSignedMeasure).toReal

lemma tvDist_eq_iSup_finPartition_abs :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  simp only [tvDist, vecTVDist, VectorMeasure.variation, preVariation, ennrealPreVariation,
    VectorMeasure.coe_sub, Pi.sub_apply, Measure.toSignedMeasure_apply,
    VectorMeasure.ennrealToMeasure_apply .univ, preVariationFun, MeasurableSet.univ, ↓reduceDIte]
  rw [ENNReal.toReal_iSup (fun _ ↦ by simp)]
  congr with P
  rw [ENNReal.toReal_sum (fun _ ↦ by simp)]
  congr with s
  simp [s.2]

end InformationTheory
