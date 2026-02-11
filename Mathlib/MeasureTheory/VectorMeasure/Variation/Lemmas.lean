/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
## Properties of variation

## Main results

* `norm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

-/

open MeasureTheory BigOperators NNReal ENNReal Function Filter

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

open Classical Finset in
/-- Measure version of `le_var_aux` which was for subadditive functions. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
  -- switch the assumption to `FinPartition`
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : ∀ t ∈ P, MeasurableSet t)
    (hP₃ : (P :Set (Set X)).PairwiseDisjoint id) : ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  let Q := Finpartition.ofPairwiseDisjoint P hP₃
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ := sorry
    _ ≤ μ.variation s := by sorry
  have h : ∑ p ∈ P, ‖μ p‖ₑ = ∑ q ∈ Q.parts, ‖μ q‖ₑ := by
    sorry
  -- define an operation for `FinPartition`, say, `ofPairwiseDisjoint`
  -- have hQ : IsInnerPart s Q := by
  --   refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp q hq hpq  ↦ ?_, fun p hp ↦ ?_⟩
  --   · exact hP₁ p (mem_filter.mp hp).1
  --   · exact hP₂ p (mem_filter.mp hp).1
  --   · exact hP₃ (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq
  --   · exact (mem_filter.mp hp).2
  refine le_of_eq_of_le h ?_
  -- use `preVariation.sum_le`
  simpa [variation] using preVariation.sum_le (fun s ↦ ‖μ s‖ₑ) hs Q

theorem norm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ ≤ variation μ E := by
  wlog hE : MeasurableSet E
  · simp [μ.not_measurable' hE]
  wlog hE' : (⟨E, hE⟩ : Subtype MeasurableSet) ≠ ⊥
  · simp only [ne_eq, not_not, ] at hE'
    rw [← MeasurableSet.subtype_bot_eq, Subtype.ext_iff] at hE'
    have : E = ∅ := by exact Set.subset_eq_empty (fun ⦃a⦄ a_1 ↦ a_1) hE'
    rw [this]
    simp
  rw [variation, preVariation, ennrealToMeasure_apply hE]
  simp only [ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

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
      _ ≤ μ.variation s := norm_measure_le_variation μ s
      _ = 0 := by
        rw [variation, preVariation, ennrealToMeasure_apply hsm]
        exact
          Eq.symm
            ((fun {x y} ↦ EReal.coe_ennreal_eq_coe_ennreal_iff.mp)
              (congrArg toEReal (id (Eq.symm hs))))
  · exact μ.not_measurable' hsm

end MeasureTheory.VectorMeasure
