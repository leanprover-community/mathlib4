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
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define integral of such vector valued measures.

When `μ` is a signed measure, it will be shown that `μ.variation E = μ.totalVariation E`. When `μ`
is `ℝ≥0∞`-valued measure, `μ.variation` coincides with `μ` on measurable sets.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

open MeasureTheory BigOperators NNReal ENNReal Function Filter Finset

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

@[simp]
lemma variation_apply (μ : VectorMeasure X V) {s : Set X} :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `le_var_aux` which was for subadditive functions. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : ∀ t ∈ P, MeasurableSet t)
    (hP₃ : (P : Set (Set X)).PairwiseDisjoint id) : ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  set Q := Finpartition.ofPairwiseDisjoint P hP₃ with hQ
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ (Finpartition.ofPairwiseDisjoint P hP₃).parts, ‖μ p‖ₑ := by
      by_cases hbot : ⊥ ∈ P
      · simp only [Finpartition.ofPairwiseDisjoint]
        rw [← erase_union_eq ⊥ P hbot, union_comm,
          sum_union_eq_right (by intro _ _ _; simp_all)]
        simp
      · have : P = (Finpartition.ofPairwiseDisjoint P hP₃).parts := by
          ext p
          simpa [Finpartition.ofPairwiseDisjoint] using (fun hp => ne_of_mem_of_not_mem hp hbot)
        simp_rw [this]
    _ ≤ ∑ p ∈ (Finpartition.extendOfLE Q (Finset.sup_le hP₁)).parts, ‖μ p‖ₑ :=
        sum_le_sum_of_subset
          (Finpartition.parts_subset_extendOfLE (Finpartition.ofPairwiseDisjoint P hP₃)
          (Finset.sup_le hP₁))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      have : p ∈ Q.parts ∨ p = s \ (P.sup id) := by
        apply Finpartition.mem_parts_or_mem_sdiff_of_mem_extendOfLE _ _ hp
      rcases this with h | h
      · rw [hQ, Finpartition.ofPairwiseDisjoint] at h
        simp only [Set.bot_eq_empty, mem_erase, ne_eq] at h
        exact hP₂ p h.2
      · simp only [sup_set_eq_biUnion, id_eq] at h
        rw [h]
        exact MeasurableSet.diff hs (measurableSet_biUnion P hP₂)

theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  · by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
    · rw [← MeasurableSet.subtype_bot_eq, Subtype.ext_iff] at hE'
      have : E = ∅ := Set.subset_eq_empty Set.Subset.rfl hE'
      simp [this]
    · rw [variation]
      simp only [preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
      calc
        ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
        _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le
  · simp [μ.not_measurable' hE]

lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero_eq_zero

lemma variation_neg {V : Type*} [NormedAddCommGroup V] (μ : MeasureTheory.VectorMeasure X V) :
    (-μ).variation = μ.variation := by simp [variation]

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · by_contra! hc
    refine (lt_self_iff_false (0 : ℝ≥0∞)).mp ?_
    calc
      0 < ‖μ s‖ₑ := enorm_pos.mpr hc
      _ ≤ μ.variation s := enorm_measure_le_variation μ s
      _ = 0 := by simpa [ennrealVariation_apply _ hsm] using hs
  · exact μ.not_measurable' hsm

end MeasureTheory.VectorMeasure
