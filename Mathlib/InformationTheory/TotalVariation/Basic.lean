/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Total variation distance between finite measures

## Main definitions

* `vecTVDist μ ν`: total variation distance between two vector measures, defined as the value on
  the universal set of the variation of `μ - ν`.
* `tvDist μ ν`: total variation distance between two finite measures, defined as the value on
  the universal set of the variation of `μ - ν`, in which both measures are seen as signed measures.

## Main statements

* `vecTVDist_self`, `vecTVDist_eq_zero_iff`, `vecTVDist_comm`, `vecTVDist_triangle`: the total
  variation distance between vector measures is a distance.
* `tvDist_self`, `tvDist_eq_zero_iff`, `tvDist_comm`, `tvDist_triangle`: the total variation
  distance between finite measures is a distance.

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

lemma vecTVDist_zero_right (μ : VectorMeasure 𝓧 M) : vecTVDist μ 0 = μ.variation Set.univ := by
  simp only [vecTVDist, sub_zero]

lemma vecTVDist_zero_left (ν : VectorMeasure 𝓧 M) : vecTVDist 0 ν = ν.variation Set.univ := by
  rw [vecTVDist_comm, vecTVDist_zero_right]

lemma vecTVDist_eq_sub_zero : vecTVDist μ ν = vecTVDist (μ - ν) 0 := by simp [vecTVDist]

end VectorMeasure

section Measure

variable {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two finite measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (vecTVDist μ.toSignedMeasure ν.toSignedMeasure).toReal

@[simp] lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [vecTVDist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congr with P
  congr with s
  simp [s.2]

lemma vecTVDist_toSignedMeasure_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure < ∞ := by
  calc vecTVDist μ.toSignedMeasure ν.toSignedMeasure
  _ ≤ vecTVDist μ.toSignedMeasure 0 + vecTVDist 0 ν.toSignedMeasure := vecTVDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by simp [vecTVDist_zero_right, vecTVDist_zero_left]
  _ < ∞ := by simp

@[simp]
lemma vecTVDist_toSignedMeasure_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure ≠ ∞ :=
  (vecTVDist_toSignedMeasure_lt_top μ ν).ne

lemma tvDist_eq_iSup_finPartition_abs :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvDist, vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs,
    ENNReal.toReal_iSup (fun _ ↦ by simp)]
  congr with P
  rw [ENNReal.toReal_sum (fun _ ↦ by simp)]
  simp

@[simp]
lemma tvDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ μ = 0 := by simp [tvDist]

@[simp]
lemma tvDist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  tvDist μ ν = 0 ↔ μ = ν := by simp [tvDist, ENNReal.toReal_eq_zero_iff]

lemma tvDist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  rw [vecTVDist_comm]

lemma tvDist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp)]
  gcongr
  · simp
  exact vecTVDist_triangle _ _ _

@[simp]
lemma tvDist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ 0 = μ.real Set.univ := by
  simp only [tvDist, vecTVDist, Measure.toSignedMeasure_zero, sub_zero,
    VectorMeasure.variation_toSignedMeasure]
  rfl

@[simp]
lemma tvDist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : tvDist 0 ν = ν.real Set.univ := by
  rw [tvDist_comm, tvDist_zero_right]

lemma tvDist_of_ge (hμν : ν ≤ μ) : tvDist μ ν = μ.real Set.univ - ν.real Set.univ := by
  calc tvDist μ ν
  _ = tvDist (μ - ν) 0 := by
    simp only [tvDist_eq_iSup_finPartition_abs, measureReal_zero, Pi.zero_apply, sub_zero]
    congr with P
    congr with s
    congr 1
    simp only [Measure.real]
    rw [Measure.sub_apply s.2 hμν, ENNReal.toReal_sub_of_le (hμν s) (by simp)]
  _ = (μ - ν).real Set.univ := by simp [tvDist_zero_right]
  _ = μ.real Set.univ - ν.real Set.univ := by
    rw [Measure.real, Measure.sub_apply .univ hμν, ENNReal.toReal_sub_of_le (hμν .univ) (by simp)]
    rfl

lemma tvDist_of_le (hμν : μ ≤ ν) : tvDist μ ν = ν.real Set.univ - μ.real Set.univ := by
  rw [tvDist_comm, tvDist_of_ge hμν]

lemma tvDist_le_add : tvDist μ ν ≤ μ.real Set.univ + ν.real Set.univ := by
  calc tvDist μ ν
  _ ≤ tvDist μ 0 + tvDist 0 ν := tvDist_triangle _ _ _
  _ = μ.real Set.univ + ν.real Set.univ := by simp [tvDist_zero_right, tvDist_zero_left]

end Measure

end InformationTheory
