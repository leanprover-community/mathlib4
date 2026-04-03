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

public section

open Finset
open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}
  [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

@[simp]
theorem ennrealToMeasure_zero {α : Type*} {m : MeasurableSpace α} :
    MeasureTheory.VectorMeasure.ennrealToMeasure (0 : VectorMeasure α ℝ≥0∞) = 0 := by
  ext s; simp [VectorMeasure.ennrealToMeasure]

@[simp]
lemma preVariation_zero_eq_zero :
    preVariation (0 : Set X → ℝ≥0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0 := by
  ext s; simp [preVariation_apply]
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
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ := by
      by_cases hbot : ⊥ ∈ P
      · simp only [Finpartition.ofPairwiseDisjoint, Set.bot_eq_empty, Q]
        rw [← erase_union_eq ⊥ P hbot, union_comm, sum_union_eq_right (by simp)]
        simp
      · have : P = Q.parts := by
          ext p
          simpa [Q, Finpartition.ofPairwiseDisjoint] using fun hp => ne_of_mem_of_not_mem hp hbot
        simp_rw [this]
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := by
        refine (Finset.sum_subset (by simp [Q']) ?_).symm
        simp_all [μ.not_measurable]
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
        sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      apply hs.diff
      simp only [sup_set_eq_biUnion, id_eq]
      exact MeasurableSet.biUnion (Finset.countable_toSet _) (by simp)

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
  exact preVariation_zero_eq_zero

@[simp]
lemma variation_neg {V : Type*} [NormedAddCommGroup V] (μ : MeasureTheory.VectorMeasure X V) :
    (-μ).variation = μ.variation := by simp [variation]

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

end MeasureTheory.VectorMeasure
