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

* `etvdist μ ν`: total variation distance between two finite measures, defined as the value on the
  whole space of the variation of `μ - ν`, in which both measures are seen as signed measures.
  This distance takes values in `ℝ≥0∞` but is always finite.
* `tvdist μ ν`: total variation distance between two finite measures,
  defined as `(etvdist μ ν).toReal`.

## Main statements

* `tvdist_self`, `tvdist_eq_zero_iff`, `tvdist_comm`, `tvdist_triangle`: the total variation
  distance between finite measures is a distance.

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two finite measures, with value in `ℝ≥0∞`. -/
noncomputable def etvdist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ≥0∞ :=
  VectorMeasure.etvdist μ.toSignedMeasure ν.toSignedMeasure

/-- Total variation distance between two finite measures, with value in `ℝ`. -/
noncomputable def tvdist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (etvdist μ ν).toReal

section ETVDist

lemma etvdist_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvdist μ ν < ∞ := by
  calc etvdist μ ν
  _ ≤ etvdist μ 0 + etvdist 0 ν := VectorMeasure.etvdist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by
    simp [etvdist]
  _ < ∞ := by simp

@[simp]
lemma etvdist_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvdist μ ν ≠ ∞ := (etvdist_lt_top μ ν).ne

lemma etvdist_eq_iSup_finPartition_enorm :
    etvdist μ ν =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [etvdist, VectorMeasure.etvdist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congrm ⨆ P, ∑ s ∈ _, ?_
  simp [s.2]

@[simp]
lemma etvdist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : etvdist μ μ = 0 := by simp [etvdist]

@[simp]
lemma etvdist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  etvdist μ ν = 0 ↔ μ = ν := by simp [etvdist]

lemma etvdist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    etvdist μ ν = etvdist ν μ := VectorMeasure.etvdist_comm _ _

lemma etvdist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    etvdist μ ξ ≤ etvdist μ ν + etvdist ν ξ := VectorMeasure.etvdist_triangle _ _ _

@[simp]
lemma etvdist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : etvdist μ 0 = μ Set.univ := by
  simp [etvdist]

@[simp]
lemma etvdist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : etvdist 0 ν = ν Set.univ := by
  simp [etvdist]

lemma etvdist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    etvdist (μ.restrict s) (ν.restrict s) + etvdist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      etvdist μ ν := by
  unfold etvdist
  rw [← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl, ← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl,
    VectorMeasure.etvdist_restrict_add_compl hs]

lemma etvdist_of_ge (hμν : ν ≤ μ) : etvdist μ ν = μ Set.univ - ν Set.univ := by
  calc etvdist μ ν
  _ = etvdist (μ - ν) 0 := by
    simp only [etvdist_eq_iSup_finPartition_enorm, measureReal_zero, Pi.zero_apply, sub_zero]
    congrm ⨆ P, ∑ s ∈ _, ‖?_‖ₑ
    simp only [Measure.real]
    rw [Measure.sub_apply s.2 hμν, ENNReal.toReal_sub_of_le (hμν s) (by simp)]
  _ = (μ - ν) Set.univ := by simp
  _ = μ Set.univ - ν Set.univ := by rw [Measure.sub_apply .univ hμν]

lemma etvdist_of_le (hμν : μ ≤ ν) : etvdist μ ν = ν Set.univ - μ Set.univ := by
  rw [etvdist_comm, etvdist_of_ge hμν]

lemma etvdist_le_add : etvdist μ ν ≤ μ Set.univ + ν Set.univ := by
  calc etvdist μ ν
  _ ≤ etvdist μ 0 + etvdist 0 ν := etvdist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by simp

end ETVDist

section TVDist

@[simp] lemma tvdist_nonneg : 0 ≤ tvdist μ ν := ENNReal.toReal_nonneg

lemma ofReal_tvdist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (tvdist μ ν) = etvdist μ ν := by
  rw [tvdist, ENNReal.ofReal_toReal (etvdist_ne_top μ ν)]

lemma tvdist_eq_iSup_finPartition_abs :
    tvdist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvdist, etvdist_eq_iSup_finPartition_enorm, ENNReal.toReal_iSup (by simp)]
  congr with P
  rw [ENNReal.toReal_sum (by simp)]
  simp

@[simp]
lemma tvdist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvdist μ μ = 0 := by simp [tvdist]

@[simp]
lemma tvdist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  tvdist μ ν = 0 ↔ μ = ν := by simp [tvdist, ENNReal.toReal_eq_zero_iff]

lemma tvdist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvdist μ ν = tvdist ν μ := by
  unfold tvdist
  rw [etvdist_comm]

lemma tvdist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    tvdist μ ξ ≤ tvdist μ ν + tvdist ν ξ := by
  unfold tvdist
  rw [← ENNReal.toReal_add (by simp) (by simp)]
  gcongr
  · simp
  exact etvdist_triangle _ _ _

@[simp]
lemma tvdist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvdist μ 0 = μ.real Set.univ := by
  simp [tvdist, Measure.real]

@[simp]
lemma tvdist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : tvdist 0 ν = ν.real Set.univ := by
  simp [tvdist, Measure.real]

lemma tvdist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    tvdist (μ.restrict s) (ν.restrict s) + tvdist (μ.restrict sᶜ) (ν.restrict sᶜ) = tvdist μ ν := by
  unfold tvdist
  rw [← ENNReal.toReal_add (by simp) (by simp), etvdist_restrict_add_compl hs]

lemma tvdist_of_ge (hμν : ν ≤ μ) : tvdist μ ν = μ.real Set.univ - ν.real Set.univ := by
  rw [tvdist, etvdist_of_ge hμν, ENNReal.toReal_sub_of_le (hμν .univ) (by simp), Measure.real,
    Measure.real]

lemma tvdist_of_le (hμν : μ ≤ ν) : tvdist μ ν = ν.real Set.univ - μ.real Set.univ := by
  rw [tvdist_comm, tvdist_of_ge hμν]

lemma tvdist_le_add : tvdist μ ν ≤ μ.real Set.univ + ν.real Set.univ := by
  calc tvdist μ ν
  _ ≤ tvdist μ 0 + tvdist 0 ν := tvdist_triangle _ _ _
  _ = μ.real Set.univ + ν.real Set.univ := by simp

end TVDist

end MeasureTheory
