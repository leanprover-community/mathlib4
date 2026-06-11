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

* `VectorMeasure.eTVDist μ ν`: total variation distance between two vector measures,
  defined as the value on the universal set of the variation of `μ - ν`.

## Main statements

* `eTVDist_self`, `eTVDist_eq_zero_iff`, `eTVDist_comm`, `eTVDist_triangle`: the total
  variation distance between vector measures is a distance.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace VectorMeasure

variable {𝓧 M : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup M] {μ ν : VectorMeasure 𝓧 M}

/-- Total variation distance between two vector measures, with value in `ℝ≥0∞`. -/
noncomputable def eTVDist (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

lemma eTVDist_eq_iSup_finPartition_enorm :
    eTVDist μ ν = ⨆ P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧))),
      ∑ x ∈ P.parts, ‖μ x - ν x‖ₑ := by
  simp [eTVDist, VectorMeasure.variation, preVariation, ennrealPreVariation,
    VectorMeasure.ennrealToMeasure_apply .univ, preVariationFun]

@[simp]
lemma eTVDist_self (μ : VectorMeasure 𝓧 M) : eTVDist μ μ = 0 := by simp [eTVDist]

@[simp]
lemma eTVDist_eq_zero_iff (μ ν : VectorMeasure 𝓧 M) : eTVDist μ ν = 0 ↔ μ = ν := by
  simp [eTVDist, sub_eq_zero]

lemma eTVDist_comm (μ ν : VectorMeasure 𝓧 M) : eTVDist μ ν = eTVDist ν μ := by
  rw [eTVDist, eTVDist, ← neg_sub, VectorMeasure.variation_neg]

lemma eTVDist_triangle (μ ν ξ : VectorMeasure 𝓧 M) :
    eTVDist μ ξ ≤ eTVDist μ ν + eTVDist ν ξ := by
  calc eTVDist μ ξ
  _ = ((μ - ν) + (ν - ξ)).variation Set.univ := by simp [eTVDist]
  _ ≤ eTVDist μ ν + eTVDist ν ξ := VectorMeasure.variation_add_le _

lemma eTVDist_zero_right (μ : VectorMeasure 𝓧 M) : eTVDist μ 0 = μ.variation Set.univ := by
  simp only [eTVDist, sub_zero]

lemma eTVDist_zero_left (ν : VectorMeasure 𝓧 M) : eTVDist 0 ν = ν.variation Set.univ := by
  rw [eTVDist_comm, eTVDist_zero_right]

lemma eTVDist_eq_eTVDist_sub_zero : eTVDist μ ν = eTVDist (μ - ν) 0 := by simp [eTVDist]

lemma eTVDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    eTVDist (μ.restrict s) (ν.restrict s) + eTVDist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      eTVDist μ ν := by
  simp_rw [eTVDist, ← VectorMeasure.restrict_sub, VectorMeasure.variation_restrict hs,
    VectorMeasure.variation_restrict hs.compl]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
  simp [← measure_union disjoint_compl_right hs.compl]

end VectorMeasure

end MeasureTheory
