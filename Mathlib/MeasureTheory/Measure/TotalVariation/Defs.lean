/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.TotalVariation

import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance

We define the total variation distance between two finite measures, as the vector total variation
distance between the corresponding signed measures.

Note that with this definition, the total variation distance between probability measures takes
values in `[0, 2]`.
Some authors prefer to define the total variation distance as half of the value defined here,
so that it takes values in `[0, 1]`.

## Main definitions

* `etvDist μ ν`: total variation distance between two finite measures, defined as the value on the
  whole space of the variation of `μ - ν`, in which both measures are seen as signed measures.
  This distance takes values in `ℝ≥0∞`. If one of the measures is not finite, it is defined to be
  `∞`, and it is finite otherwise (see `etvDist_lt_top_iff`).
* `tvDist μ ν`: total variation distance between two finite measures,
  defined as `(etvDist μ ν).toReal`. It is equal to `0` if one of the measures is not finite.

## Main statements

* `tvDist_self`, `tvDist_eq_zero_iff`, `tvDist_comm`, `tvDist_triangle`: the total variation
  distance between finite measures is a distance.

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧}

open Classical in
/-- Total variation distance between two finite measures, with value in `ℝ≥0∞`.
If one of the measures is not finite, it is defined to be `∞`. -/
@[no_expose] noncomputable def etvDist (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  if h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν then
    haveI := h.1
    haveI := h.2
    VectorMeasure.etvDist μ.toSignedMeasure ν.toSignedMeasure
  else ∞

/-- Total variation distance between two finite measures, with value in `ℝ`.
If one of the measures is not finite, it is equal to `0`. -/
noncomputable def tvDist (μ ν : Measure 𝓧) : ℝ := (etvDist μ ν).toReal

section ETVDist

lemma etvDist_eq_etvDist_toSignedMeasure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvDist μ ν = VectorMeasure.etvDist μ.toSignedMeasure ν.toSignedMeasure := by
  rw [etvDist, dite_eq_left ⟨‹_›, ‹_›⟩]

lemma etvDist_of_not_isFiniteMeasure (h : ¬ (IsFiniteMeasure μ ∧ IsFiniteMeasure ν)) :
    etvDist μ ν = ∞ := by
  rw [etvDist, dite_eq_right h]

lemma etvDist_of_not_isFiniteMeasure_left (h : ¬ IsFiniteMeasure μ) : etvDist μ ν = ∞ :=
  etvDist_of_not_isFiniteMeasure (by tauto)

lemma etvDist_of_not_isFiniteMeasure_right (h : ¬ IsFiniteMeasure ν) : etvDist μ ν = ∞ :=
  etvDist_of_not_isFiniteMeasure (by tauto)

lemma etvDist_comm (μ ν : Measure 𝓧) : etvDist μ ν = etvDist ν μ := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    simp only [etvDist_eq_etvDist_toSignedMeasure]
    exact VectorMeasure.etvDist_comm _ _
  · rw [etvDist_of_not_isFiniteMeasure h, etvDist_of_not_isFiniteMeasure (by tauto)]

@[simp]
lemma etvDist_zero_right (μ : Measure 𝓧) : etvDist μ 0 = μ Set.univ := by
  by_cases hμ : IsFiniteMeasure μ
  · simp [etvDist_eq_etvDist_toSignedMeasure]
  · rw [etvDist_of_not_isFiniteMeasure_left hμ, not_isFiniteMeasure_iff.mp hμ]

@[simp]
lemma etvDist_zero_left (ν : Measure 𝓧) : etvDist 0 ν = ν Set.univ := by
  rw [etvDist_comm, etvDist_zero_right]

lemma etvDist_triangle (μ ν ξ : Measure 𝓧) : etvDist μ ξ ≤ etvDist μ ν + etvDist ν ξ := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ IsFiniteMeasure ξ
  · obtain ⟨_, _, _⟩ := h
    simp only [etvDist_eq_etvDist_toSignedMeasure]
    exact VectorMeasure.etvDist_triangle _ _ _
  simp only [not_and_or] at h
  rcases h with h | h | h <;>
    simp [etvDist_of_not_isFiniteMeasure_left h, etvDist_of_not_isFiniteMeasure_right h]

lemma etvDist_le_add : etvDist μ ν ≤ μ Set.univ + ν Set.univ := by
  calc etvDist μ ν
  _ ≤ etvDist μ 0 + etvDist 0 ν := etvDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by simp

lemma etvDist_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvDist μ ν < ∞ :=
  etvDist_le_add.trans_lt (by simp)

@[simp]
lemma etvDist_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvDist μ ν ≠ ∞ := (etvDist_lt_top μ ν).ne

lemma etvDist_lt_top_iff : etvDist μ ν < ∞ ↔ IsFiniteMeasure μ ∧ IsFiniteMeasure ν := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ etvDist_lt_top μ ν⟩
  by_contra h'
  simp [etvDist_of_not_isFiniteMeasure h'] at h

lemma etvDist_ne_top_iff : etvDist μ ν ≠ ∞ ↔ IsFiniteMeasure μ ∧ IsFiniteMeasure ν := by
  rw [← lt_top_iff_ne_top, etvDist_lt_top_iff]

lemma etvDist_eq_iSup_finPartition_enorm [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvDist μ ν =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congrm ⨆ P, ∑ s ∈ _, ?_
  simp [s.2]

@[simp]
lemma etvDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : etvDist μ μ = 0 := by
  simp [etvDist_eq_etvDist_toSignedMeasure]

@[simp]
lemma etvDist_eq_zero_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvDist μ ν = 0 ↔ μ = ν := by
  simp [etvDist_eq_etvDist_toSignedMeasure]

lemma etvDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    etvDist (μ.restrict s) (ν.restrict s) + etvDist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    simp only [etvDist_eq_etvDist_toSignedMeasure]
    rw [← VectorMeasure.restrict_toSignedMeasure hs,
      ← VectorMeasure.restrict_toSignedMeasure hs.compl,
      ← VectorMeasure.restrict_toSignedMeasure hs,
      ← VectorMeasure.restrict_toSignedMeasure hs.compl,
      VectorMeasure.etvDist_restrict_add_compl hs]
  · rw [etvDist_of_not_isFiniteMeasure h, ENNReal.add_eq_top]
    by_contra! h'
    simp only [etvDist_ne_top_iff, isFiniteMeasure_restrict] at h'
    refine h ⟨⟨?_⟩, ⟨?_⟩⟩ <;> rw [← measure_add_measure_compl hs] <;> simp [h', lt_top_iff_ne_top]

lemma etvDist_of_ge [IsFiniteMeasure ν] (hμν : ν ≤ μ) :
    etvDist μ ν = μ Set.univ - ν Set.univ := by
  by_cases hμ : IsFiniteMeasure μ
  · calc etvDist μ ν
    _ = etvDist (μ - ν) 0 := by
      simp only [etvDist_eq_iSup_finPartition_enorm, measureReal_zero, Pi.zero_apply, sub_zero]
      congrm ⨆ P, ∑ s ∈ _, ‖?_‖ₑ
      simp only [Measure.real]
      rw [Measure.sub_apply s.2 hμν, ENNReal.toReal_sub_of_le (hμν s) (by simp)]
    _ = (μ - ν) Set.univ := by simp
    _ = μ Set.univ - ν Set.univ := by rw [Measure.sub_apply .univ hμν]
  · rw [etvDist_of_not_isFiniteMeasure_left hμ, not_isFiniteMeasure_iff.mp hμ,
      ENNReal.sub_eq_top_iff.2 ⟨rfl, measure_ne_top _ _⟩]

lemma etvDist_of_le [IsFiniteMeasure μ] (hμν : μ ≤ ν) :
    etvDist μ ν = ν Set.univ - μ Set.univ := by
  rw [etvDist_comm, etvDist_of_ge hμν]

end ETVDist

section TVDist

@[simp] lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma tvDist_of_not_isFiniteMeasure (h : ¬ (IsFiniteMeasure μ ∧ IsFiniteMeasure ν)) :
    tvDist μ ν = 0 := by
  simp [tvDist, etvDist_of_not_isFiniteMeasure h]

lemma tvDist_of_not_isFiniteMeasure_left (h : ¬ IsFiniteMeasure μ) : tvDist μ ν = 0 :=
  tvDist_of_not_isFiniteMeasure (by tauto)

lemma tvDist_of_not_isFiniteMeasure_right (h : ¬ IsFiniteMeasure ν) : tvDist μ ν = 0 :=
  tvDist_of_not_isFiniteMeasure (by tauto)

lemma ofReal_tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (tvDist μ ν) = etvDist μ ν := by
  rw [tvDist, ENNReal.ofReal_toReal (etvDist_ne_top μ ν)]

lemma tvDist_eq_iSup_finPartition_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvDist, etvDist_eq_iSup_finPartition_enorm, ENNReal.toReal_iSup (by simp)]
  congr with P
  rw [ENNReal.toReal_sum (by simp)]
  simp

@[simp]
lemma tvDist_self (μ : Measure 𝓧) : tvDist μ μ = 0 := by
  by_cases hμ : IsFiniteMeasure μ
  · simp [tvDist]
  · exact tvDist_of_not_isFiniteMeasure_left hμ

@[simp]
lemma tvDist_eq_zero_iff {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = 0 ↔ μ = ν := by simp [tvDist, ENNReal.toReal_eq_zero_iff]

lemma tvDist_comm (μ ν : Measure 𝓧) : tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  rw [etvDist_comm]

lemma tvDist_triangle (μ ν ξ : Measure 𝓧) [IsFiniteMeasure ν] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ξ
  · obtain ⟨_, _⟩ := h
    unfold tvDist
    rw [← ENNReal.toReal_add (by simp) (by simp)]
    gcongr
    · simp
    exact etvDist_triangle _ _ _
  · rw [tvDist_of_not_isFiniteMeasure h]
    exact add_nonneg tvDist_nonneg tvDist_nonneg

@[simp]
lemma tvDist_zero_right (μ : Measure 𝓧) : tvDist μ 0 = μ.real Set.univ := by
  simp [tvDist, Measure.real]

@[simp]
lemma tvDist_zero_left (ν : Measure 𝓧) : tvDist 0 ν = ν.real Set.univ := by
  simp [tvDist, Measure.real]

lemma tvDist_restrict_add_compl [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set 𝓧}
    (hs : MeasurableSet s) :
    tvDist (μ.restrict s) (ν.restrict s) + tvDist (μ.restrict sᶜ) (ν.restrict sᶜ) = tvDist μ ν := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp), etvDist_restrict_add_compl hs]

lemma tvDist_of_ge [IsFiniteMeasure μ] (hμν : ν ≤ μ) :
    tvDist μ ν = μ.real Set.univ - ν.real Set.univ := by
  have := isFiniteMeasure_of_le μ hμν
  rw [tvDist, etvDist_of_ge hμν, ENNReal.toReal_sub_of_le (hμν .univ) (by simp), Measure.real,
    Measure.real]

lemma tvDist_of_le [IsFiniteMeasure ν] (hμν : μ ≤ ν) :
    tvDist μ ν = ν.real Set.univ - μ.real Set.univ := by
  rw [tvDist_comm, tvDist_of_ge hμν]

lemma tvDist_le_add : tvDist μ ν ≤ μ.real Set.univ + ν.real Set.univ := by
  calc tvDist μ ν
  _ ≤ tvDist μ 0 + tvDist 0 ν := tvDist_triangle _ _ _
  _ = μ.real Set.univ + ν.real Set.univ := by simp

end TVDist

end MeasureTheory
