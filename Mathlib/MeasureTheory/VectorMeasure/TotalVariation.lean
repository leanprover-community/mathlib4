/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance of vector measures

We define the total variation distance between two vector measures `μ, ν` as
`(μ - ν).variation Set.univ`.

## Main definitions

* `VectorMeasure.etvdist μ ν`: total variation distance between two vector measures,
  defined as the value on the universal set of the variation of `μ - ν`.

## Main statements

* `etvdist_self`, `etvdist_eq_zero_iff`, `etvdist_comm`, `etvdist_triangle`: the total
  variation distance between vector measures is a distance.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace VectorMeasure

variable {𝓧 M : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup M] {μ ν : VectorMeasure 𝓧 M}

/-- Total variation distance between two vector measures, with value in `ℝ≥0∞`. -/
noncomputable def etvdist (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

lemma etvdist_eq_iSup_finPartition_enorm :
    etvdist μ ν = ⨆ P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧))),
      ∑ x ∈ P.parts, ‖μ x - ν x‖ₑ := by
  simp [etvdist, variation, preVariation, ennrealPreVariation,
    ennrealToMeasure_apply .univ, preVariationFun]

@[simp]
lemma etvdist_self (μ : VectorMeasure 𝓧 M) : etvdist μ μ = 0 := by simp [etvdist]

@[simp]
lemma etvdist_eq_zero_iff (μ ν : VectorMeasure 𝓧 M) : etvdist μ ν = 0 ↔ μ = ν := by
  simp [etvdist, sub_eq_zero]

lemma etvdist_comm (μ ν : VectorMeasure 𝓧 M) : etvdist μ ν = etvdist ν μ := by
  rw [etvdist, etvdist, ← neg_sub, variation_neg]

lemma etvdist_triangle (μ ν ξ : VectorMeasure 𝓧 M) :
    etvdist μ ξ ≤ etvdist μ ν + etvdist ν ξ := by
  calc etvdist μ ξ
  _ = ((μ - ν) + (ν - ξ)).variation Set.univ := by simp [etvdist]
  _ ≤ etvdist μ ν + etvdist ν ξ := variation_add_le _

@[simp]
lemma etvdist_zero_right (μ : VectorMeasure 𝓧 M) : etvdist μ 0 = μ.variation Set.univ := by
  simp only [etvdist, sub_zero]

@[simp]
lemma etvdist_zero_left (ν : VectorMeasure 𝓧 M) : etvdist 0 ν = ν.variation Set.univ := by
  rw [etvdist_comm, etvdist_zero_right]

lemma etvdist_eq_etvdist_sub_zero : etvdist μ ν = etvdist (μ - ν) 0 := by simp [etvdist]

lemma etvdist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    etvdist (μ.restrict s) (ν.restrict s) + etvdist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      etvdist μ ν := by
  simp [etvdist, ← restrict_sub, variation_restrict hs, variation_restrict hs.compl,
    MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    ← measure_union disjoint_compl_right hs.compl]

end VectorMeasure

end MeasureTheory
