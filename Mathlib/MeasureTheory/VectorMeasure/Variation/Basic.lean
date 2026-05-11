/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset
open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `sum_le_preVariationFun_of_subset`. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : ∀ t ∈ Q'.parts, t ⊆ s := by simp [Q', Q]; grind
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
      exact hs.diff <| .biUnion (Finset.countable_toSet _) (by simp)

theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [μ.not_measurable' hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

lemma variation_apply_le_of_forall_enorm_le {μ : VectorMeasure X V} {ν : Measure X} {s : Set X}
    (hs : MeasurableSet s) (hν : ∀ (t : Set X), MeasurableSet t → t ⊆ s → ‖μ t‖ₑ ≤ ν t) :
    μ.variation s ≤ ν s := by
  simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
    ennrealPreVariation_apply, preVariationFun, hs, ↓reduceDIte, iSup_le_iff]
  intro P
  calc ∑ t ∈ P.parts, ‖μ t‖ₑ
  _ ≤ ∑ t ∈ P.parts, ν t := by
    gcongr with t ht
    apply hν _ t.2 (P.le ht)
  _ = ν (⋃ t ∈ P.parts, t) := by
    rw [measure_biUnion_finset _ (fun i hi ↦ i.2)]
    intro i hi j hj hij
    simpa [Function.onFun, disjoint_iff, Subtype.ext_iff] using P.disjoint hi hj hij
  _ ≤ ν s := by
    gcongr
    simp only [Set.iUnion_subset_iff]
    intro t ht
    exact P.le ht

/-- Characterization of the variation as the minimal measure larger than `‖μ ·‖`. -/
lemma variation_le_of_forall_enorm_le {μ : VectorMeasure X V} {ν : Measure X}
    (hν : ∀ (s : Set X), MeasurableSet s → ‖μ s‖ₑ ≤ ν s) :
    μ.variation ≤ ν :=
  Measure.le_iff.2 (fun _ hs ↦ variation_apply_le_of_forall_enorm_le hs (fun t ht _ ↦ hν t ht))

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

lemma variation_restrict (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    (μ.restrict s).variation = μ.variation.restrict s := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variation (t ∩ s)
    _ ≤ (μ.restrict s).variation (t ∩ s) := by
      apply variation_apply_le_of_forall_enorm_le (ht.inter hs) (fun u u_meas hu ↦ ?_)
      have : μ u = μ.restrict s u := by
        rw [VectorMeasure.restrict_apply _ hs u_meas]
        congr
        grind
      rw [this]
      apply enorm_measure_le_variation
    _ ≤ (μ.restrict s).variation t := by
      gcongr
      exact Set.inter_subset_left

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ : VectorMeasure X V}

theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E ≠ ∞ := by finiteness) :
    ‖μ E‖ ≤ μ.variation.real E := by
  rw [measureReal_def, ← toReal_enorm, ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]

end NormedAddCommGroup

end MeasureTheory.VectorMeasure
