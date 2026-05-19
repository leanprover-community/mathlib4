/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.MulAction

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
  [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

@[simp]
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

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero

@[simp]
lemma variation_neg {V : Type*} [NormedAddCommGroup V] (μ : MeasureTheory.VectorMeasure X V) :
    (-μ).variation = μ.variation := by simp [variation]

@[simp]
lemma variation_smul {V : Type*} [NormedAddCommGroup V]
    {R : Type*} [SeminormedRing R] [DistribMulAction R V] [ContinuousConstSMul R V]
    [NormSMulClass R V]
    (μ : MeasureTheory.VectorMeasure X V) (r : R) :
    (r • μ).variation = ENNReal.ofReal (‖r‖) • μ.variation := by
  simp only [variation, coe_smul, Pi.smul_apply]
  ext E hE
  simp [preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply, preVariationFun,
    ENNReal.mul_iSup, Finset.mul_sum, enorm_smul]

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

lemma variation_le_of_forall_enorm_le (μ : VectorMeasure X V) (ν : Measure X)
    (h : ∀ E, MeasurableSet E → ‖μ E‖ₑ ≤ ν E) :
    μ.variation ≤ ν := by
  apply Measure.le_intro
  intro s hs _
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x ∈ i.parts, ‖μ x‖ₑ ≤ ∑ x ∈ i.parts, ν x := by
      exact Finset.sum_le_sum (by intro s hs; exact h s s.property)
    _ = ν (i.parts.sup Subtype.val) := by
      rw [sup_set_eq_biUnion]
      symm
      apply MeasureTheory.measure_biUnion_finset
      · have := i.supIndep
        rw [Finset.supIndep_iff_pairwiseDisjoint] at this
        intro a ha b hb hab
        have h := i.disjoint ha hb hab
        simp only [Function.onFun, id] at h ⊢
        simp only [Set.disjoint_iff_inter_eq_empty]
        exact congr_arg Subtype.val (le_bot_iff.mp (disjoint_iff_inf_le.mp h))
      · intro b hb; exact b.property
    _ ≤ ν s := by
      apply measure_mono
      rw [sup_set_eq_biUnion]
      exact Set.iUnion₂_subset (by intro _ hp; exact Subtype.coe_le_coe.mpr (i.le hp))

lemma variation_eq_of_forall_enorm_eq (μ ν : VectorMeasure X V)
    (h : ∀ E, MeasurableSet E → ‖μ E‖ₑ = ‖ν E‖ₑ) :
    μ.variation = ν.variation := by
    apply le_antisymm
    · apply variation_le_of_forall_enorm_le
      intro E hE
      rw [h E hE]
      exact enorm_measure_le_variation ν E
    · apply variation_le_of_forall_enorm_le
      intro E hE
      rw [← h E hE]
      exact enorm_measure_le_variation μ E

lemma variation_add_le [ContinuousAdd V] (μ ν : VectorMeasure X V) :
    variation (μ + ν) ≤ variation μ + variation ν := by
  apply variation_le_of_forall_enorm_le
  intro E _
  simp only [coe_add, Pi.add_apply, Measure.coe_add]
  calc
    ‖μ E + ν E‖ₑ ≤ ‖μ E‖ₑ + ‖ν E‖ₑ := (enorm_add_le _ _)
    _ ≤ μ.variation E + ν.variation E := by
      apply add_le_add <;> exact enorm_measure_le_variation _ E

end MeasureTheory.VectorMeasure
