/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
## Properties of variation

## Main results

* `norm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.
* `variation_of_ENNReal`: if `μ` is `VectorMeasure X ℝ≥0∞` then `variation μ = μ`.
-/

@[expose] public section

open MeasureTheory BigOperators NNReal ENNReal Function Filter

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

open Classical Finset in
/-- Measure version of `le_var_aux` which was for subadditive functions. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s)
    (hP₂ : ∀ t ∈ P, MeasurableSet t) (hP₃ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  let Q := P.filter (· ≠ ∅)
  have h : ∑ p ∈ P, ‖μ p‖ₑ = ∑ q ∈ Q, ‖μ q‖ₑ := by
    refine Eq.symm (sum_filter_of_ne fun p hp h ↦ ?_)
    by_contra! hc
    simp_all
  have hQ : IsInnerPart s Q := by
    refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp q hq hpq  ↦ ?_, fun p hp ↦ ?_⟩
    · exact hP₁ p (mem_filter.mp hp).1
    · exact hP₂ p (mem_filter.mp hp).1
    · exact hP₃ (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq
    · exact (mem_filter.mp hp).2
  refine le_of_eq_of_le h ?_
  simpa [variation] using le_var_aux (fun s ↦ ‖μ s‖ₑ) hs hQ

theorem norm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ ≤ variation μ E := by
  wlog hE' : E ≠ ∅
  · simp [not_ne_iff.mp hE']
  wlog hE : MeasurableSet E
  · simp [μ.not_measurable' hE]
  have h : {E} ∈ {P | IsInnerPart E P} := by simpa using isInnerPart_self hE hE'
  have := le_biSup (fun P ↦ ∑ p ∈ P, ‖μ p‖ₑ) h
  simp_all [variation, var_aux]

lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  ext _ _
  simp [variation, var_aux_zero]

lemma variation_neg
    (μ : MeasureTheory.ComplexMeasure X) : (-μ).variation = μ.variation := by
  simp [variation]

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.variation := by
  intro s hs
  by_contra! hc
  refine (lt_self_iff_false (0 : ℝ≥0∞)).mp ?_
  calc
    0 < ‖μ s‖ₑ := enorm_pos.mpr hc
    _ ≤ μ.variation s := norm_measure_le_variation μ s
    _ = 0 := hs

-- TO DO: move this to a good home or incorporate in proof.
lemma monotone_of_ENNReal  {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂)
    (h : s₁ ⊆ s₂) (μ : VectorMeasure X ℝ≥0∞) : μ s₁ ≤ μ s₂ := by
  simp [← VectorMeasure.of_add_of_diff (v := μ) hs₁ hs₂ h]

-- TO DO: move this to a good home or could more mathlib style choices earlier make this redundant?
open Classical in
lemma biUnion_Finset (μ : VectorMeasure X ℝ≥0∞) {S : Finset (Set X)}
    (hS : ∀ s ∈ S, MeasurableSet s) (hS' : S.toSet.PairwiseDisjoint id) :
    ∑ s ∈ S, μ s = μ (⋃ s ∈ S, s) := by
  have : ⋃ s ∈ S, s = ⋃ i : S, i.val := by apply Set.biUnion_eq_iUnion
  rw [this, μ.of_disjoint_iUnion]
  · simp
  · simpa
  · intro p q h
    exact hS' p.property q.property (Subtype.coe_ne_coe.mpr h)

/-- The variation of an `ℝ≥0∞`-valued measure is the measure itself. -/
lemma variation_of_ENNReal (μ : VectorMeasure X ℝ≥0∞) : variation μ = μ := by
  ext s hs
  simp only [variation, var_aux, hs, reduceIte]
  apply eq_of_le_of_le
  · simp only [enorm_eq_self, iSup_le_iff]
    intro P hP
    have : ∑ x ∈ P, μ x  =  μ (⋃ p ∈ P, p) := by
      exact biUnion_Finset μ hP.2.1 hP.2.2.1
    rw [this]
    apply monotone_of_ENNReal (Finset.measurableSet_biUnion P hP.2.1) (hs) (Set.iUnion₂_subset hP.1)
  · by_cases hc : s ≠ ∅
    · have h : {s} ∈ {P | IsInnerPart s P} := by simpa using isInnerPart_self hs hc
      have := le_biSup (fun P ↦ ∑ x ∈ P, μ x) h
      simp_all
    · push_neg at hc
      simp [hc]

end MeasureTheory.VectorMeasure
