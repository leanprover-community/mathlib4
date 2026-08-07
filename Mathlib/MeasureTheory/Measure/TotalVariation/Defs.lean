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

* `eTVDist μ ν`: total variation distance between two finite measures, defined as the value on the
  universal set of the variation of `μ - ν`, in which both measures are seen as signed measures.
  This distance takes values in `ℝ≥0∞` but is always finite.
* `tvDist μ ν`: total variation distance between two finite measures,
  defined as `(eTVDist μ ν).toReal`.

## Main statements

* `tvDist_self`, `tvDist_eq_zero_iff`, `tvDist_comm`, `tvDist_triangle`: the total variation
  distance between finite measures is a distance.

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two finite measures, with value in `ℝ≥0∞`. -/
noncomputable def eTVDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ≥0∞ :=
  VectorMeasure.eTVDist μ.toSignedMeasure ν.toSignedMeasure

/-- Total variation distance between two finite measures, with value in `ℝ`. -/
noncomputable def tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (eTVDist μ ν).toReal

section ETVDist

lemma eTVDist_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    eTVDist μ ν < ∞ := by
  calc eTVDist μ ν
  _ ≤ eTVDist μ 0 + eTVDist 0 ν := VectorMeasure.eTVDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by
    simp [eTVDist, VectorMeasure.eTVDist_zero_right, VectorMeasure.eTVDist_zero_left]
  _ < ∞ := by simp

@[simp]
lemma eTVDist_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    eTVDist μ ν ≠ ∞ := (eTVDist_lt_top μ ν).ne

lemma eTVDist_eq_iSup_finPartition_abs :
    eTVDist μ ν =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [eTVDist, VectorMeasure.eTVDist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congr with P
  congr with s
  simp [s.2]

@[simp]
lemma eTVDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : eTVDist μ μ = 0 := by simp [eTVDist]

@[simp]
lemma eTVDist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  eTVDist μ ν = 0 ↔ μ = ν := by simp [eTVDist]

lemma eTVDist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    eTVDist μ ν = eTVDist ν μ := VectorMeasure.eTVDist_comm _ _

lemma eTVDist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    eTVDist μ ξ ≤ eTVDist μ ν + eTVDist ν ξ := VectorMeasure.eTVDist_triangle _ _ _

@[simp]
lemma eTVDist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : eTVDist μ 0 = μ Set.univ := by
  simp [eTVDist]

@[simp]
lemma eTVDist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : eTVDist 0 ν = ν Set.univ := by
  simp [eTVDist]

lemma eTVDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    eTVDist (μ.restrict s) (ν.restrict s) + eTVDist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      eTVDist μ ν := by
  unfold eTVDist
  rw [← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl, ← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl,
    VectorMeasure.eTVDist_restrict_add_compl hs]

lemma eTVDist_of_ge (hμν : ν ≤ μ) : eTVDist μ ν = μ Set.univ - ν Set.univ := by
  calc eTVDist μ ν
  _ = eTVDist (μ - ν) 0 := by
    simp only [eTVDist_eq_iSup_finPartition_abs, measureReal_zero, Pi.zero_apply, sub_zero]
    congr with P
    congr with s
    congr 1
    simp only [Measure.real]
    rw [Measure.sub_apply s.2 hμν, ENNReal.toReal_sub_of_le (hμν s) (by simp)]
  _ = (μ - ν) Set.univ := by simp
  _ = μ Set.univ - ν Set.univ := by rw [Measure.sub_apply .univ hμν]

lemma eTVDist_of_le (hμν : μ ≤ ν) : eTVDist μ ν = ν Set.univ - μ Set.univ := by
  rw [eTVDist_comm, eTVDist_of_ge hμν]

lemma eTVDist_le_add : eTVDist μ ν ≤ μ Set.univ + ν Set.univ := by
  calc eTVDist μ ν
  _ ≤ eTVDist μ 0 + eTVDist 0 ν := eTVDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by simp [eTVDist_zero_right, eTVDist_zero_left]

end ETVDist

section TVDist

@[simp] lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma ofReal_tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (tvDist μ ν) = eTVDist μ ν := by
  rw [tvDist, ENNReal.ofReal_toReal (eTVDist_ne_top μ ν)]

lemma tvDist_eq_iSup_finPartition_abs :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvDist, eTVDist_eq_iSup_finPartition_abs, ENNReal.toReal_iSup (by simp)]
  congr with P
  rw [ENNReal.toReal_sum (by simp)]
  simp

@[simp]
lemma tvDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ μ = 0 := by simp [tvDist]

@[simp]
lemma tvDist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  tvDist μ ν = 0 ↔ μ = ν := by simp [tvDist, ENNReal.toReal_eq_zero_iff]

lemma tvDist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  rw [eTVDist_comm]

lemma tvDist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp)]
  gcongr
  · simp
  exact eTVDist_triangle _ _ _

@[simp]
lemma tvDist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ 0 = μ.real Set.univ := by
  simp [tvDist, Measure.real]

@[simp]
lemma tvDist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : tvDist 0 ν = ν.real Set.univ := by
  simp [tvDist, Measure.real]

lemma tvDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    tvDist (μ.restrict s) (ν.restrict s) + tvDist (μ.restrict sᶜ) (ν.restrict sᶜ) = tvDist μ ν := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp), eTVDist_restrict_add_compl hs]

lemma tvDist_of_ge (hμν : ν ≤ μ) : tvDist μ ν = μ.real Set.univ - ν.real Set.univ := by
  rw [tvDist, eTVDist_of_ge hμν, ENNReal.toReal_sub_of_le (hμν .univ) (by simp), Measure.real,
    Measure.real]

lemma tvDist_of_le (hμν : μ ≤ ν) : tvDist μ ν = ν.real Set.univ - μ.real Set.univ := by
  rw [tvDist_comm, tvDist_of_ge hμν]

lemma tvDist_le_add : tvDist μ ν ≤ μ.real Set.univ + ν.real Set.univ := by
  calc tvDist μ ν
  _ ≤ tvDist μ 0 + tvDist 0 ν := tvDist_triangle _ _ _
  _ = μ.real Set.univ + ν.real Set.univ := by simp [tvDist_zero_right, tvDist_zero_left]

end TVDist

end MeasureTheory
