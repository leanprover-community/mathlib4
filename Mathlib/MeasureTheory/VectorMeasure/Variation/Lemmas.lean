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

end MeasureTheory.VectorMeasure
