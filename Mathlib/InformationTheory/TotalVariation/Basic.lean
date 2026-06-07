/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance between finite measures

## Main definitions

* `vecTVDist μ ν`: total variation distance between two vector measures, defined as the value on
  the universal set of the variation of `μ - ν`.
* `tvDist μ ν`: total variation distance, defined as the value on the universal set of
  the variation of `μ - ν`, in which both measures are seen as signed measures.

## Main statements

* `fooBar_unique`

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

section VectorMeasure

variable {M : Type*} [NormedAddCommGroup M] {μ ν : VectorMeasure 𝓧 M}

/-- Total variation distance between two vector measures. -/
noncomputable def vecTVDist {M : Type*} [NormedAddCommGroup M]
    (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

lemma vecTVDist_eq_iSup_finPartition_enorm :
    vecTVDist μ ν = ⨆ P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧))),
      ∑ x ∈ P.parts, ‖μ x - ν x‖ₑ := by
  simp [vecTVDist, VectorMeasure.variation, preVariation, ennrealPreVariation,
    VectorMeasure.ennrealToMeasure_apply .univ, preVariationFun]

@[simp]
lemma vecTVDist_self (μ : VectorMeasure 𝓧 M) : vecTVDist μ μ = 0 := by simp [vecTVDist]

@[simp]
lemma vecTVDist_eq_zero_iff (μ ν : VectorMeasure 𝓧 M) : vecTVDist μ ν = 0 ↔ μ = ν := by
  simp [vecTVDist, sub_eq_zero]

lemma vecTVDist_comm (μ ν : VectorMeasure 𝓧 M) : vecTVDist μ ν = vecTVDist ν μ := by
  unfold vecTVDist
  rw [← neg_sub, VectorMeasure.variation_neg]

lemma vecTVDist_triangle (μ ν ξ : VectorMeasure 𝓧 M) :
    vecTVDist μ ξ ≤ vecTVDist μ ν + vecTVDist ν ξ := by
  calc vecTVDist μ ξ
  _ = ((μ - ν) + (ν - ξ)).variation Set.univ := by simp [vecTVDist]
  _ ≤ vecTVDist μ ν + vecTVDist ν ξ := VectorMeasure.variation_add_le _

end VectorMeasure

section Measure

variable {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two finite measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (vecTVDist μ.toSignedMeasure ν.toSignedMeasure).toReal

lemma vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [vecTVDist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congr with P
  congr with s
  simp [s.2]

lemma tvDist_eq_iSup_finPartition_abs :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvDist, vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs,
    ENNReal.toReal_iSup (fun _ ↦ by simp)]
  congr with P
  rw [ENNReal.toReal_sum (fun _ ↦ by simp)]
  simp

lemma vecTVDist_toSignedMeasure_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure < ∞ := by
  rw [vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs]
  sorry

@[simp]
lemma vecTVDist_toSignedMeasure_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure ≠ ∞ :=
  (vecTVDist_toSignedMeasure_lt_top μ ν).ne

@[simp]
lemma tvDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ μ = 0 := by simp [tvDist]

@[simp]
lemma tvDist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  tvDist μ ν = 0 ↔ μ = ν := by simp [tvDist, ENNReal.toReal_eq_zero_iff]; sorry

lemma tvDist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  rw [vecTVDist_comm]

lemma tvDist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  rw [← ENNReal.toReal_add]
  rotate_left
  · exact vecTVDist_toSignedMeasure_ne_top _ _
  · exact vecTVDist_toSignedMeasure_ne_top _ _
  gcongr
  · simp
  exact vecTVDist_triangle _ _ _

end Measure

end InformationTheory
