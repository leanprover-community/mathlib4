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

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ ν : VectorMeasure X V}

theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E ≠ ∞ := by finiteness) :
    ‖μ E‖ ≤ μ.variation.real E := by
  rw [measureReal_def, ← toReal_enorm, ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]

lemma variation_add_le : (μ + ν).variation ≤ μ.variation + ν.variation := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  simp only [variation_apply, preVariation_apply, Measure.add_apply, ennrealToMeasure_apply hs,
    ennrealPreVariation_apply, preVariationFun, hs, ↓reduceDIte]
  refine iSup_le fun P ↦ ?_
  calc
  _ ≤ ∑ p ∈ P.parts, (‖μ p‖ₑ + ‖ν p‖ₑ) := Finset.sum_le_sum fun p _ ↦ enorm_add_le (μ p) (ν p)
  _ = (∑ p ∈ P.parts, ‖μ p‖ₑ) + ∑ p ∈ P.parts, ‖ν p‖ₑ := by rw [Finset.sum_add_distrib]
  _ ≤ _ := add_le_add (le_iSup_of_le P le_rfl) (le_iSup_of_le P le_rfl)

lemma variation_sub_le : (μ - ν).variation ≤ μ.variation + ν.variation := by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]

lemma variation_finsetSum_le {ι} (s : Finset ι) (μ : ι → VectorMeasure X V) :
    (∑ i ∈ s, μ i).variation ≤ ∑ i ∈ s, (μ i).variation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))

end NormedAddCommGroup

end MeasureTheory.VectorMeasure
