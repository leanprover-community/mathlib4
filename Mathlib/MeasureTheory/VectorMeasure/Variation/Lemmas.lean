/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
## Properties of variation

## Main results

* `norm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

-/

open MeasureTheory BigOperators NNReal ENNReal Function Filter Set

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

open Classical Finset in
/-- Measure version of `le_var_aux` which was for subadditive functions. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : ∀ t ∈ P, MeasurableSet t) (hP₃ : P.toSet.PairwiseDisjoint id) :
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

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  ext _ _
  simp [variation, var_aux_zero]

theorem eq_zero_of_zero_variation (μ : VectorMeasure X V) : μ.variation = 0 → μ = 0 := by
  intro hμ; ext E hE; simp only [coe_zero, Pi.zero_apply, ← enorm_eq_zero (a := μ E)]
  refine le_antisymm ?_ (zero_le _)
  refine le_of_le_of_eq (norm_measure_le_variation μ E) ?_
  have : ↑μ.variation = fun E ↦ 0 := by simp_all only [coe_zero]; rfl
  exact congr_fun this E

theorem eq_zero_of_zero_variation_ennrealToMeasure (μ : VectorMeasure X V) :
    μ.variation.ennrealToMeasure = 0 → μ = 0 := by
  intro hμ; apply eq_zero_of_zero_variation
  rw [← Measure.toENNRealVectorMeasure_ennrealToMeasure μ.variation, hμ,
    Measure.toENNRealVectorMeasure_zero]

theorem eq_zero_of_zero_variation_ennrealToMeasure_univ (μ : VectorMeasure X V) :
    μ.variation.ennrealToMeasure Set.univ = 0 → μ = 0 := by
  intro hμ; apply eq_zero_of_zero_variation_ennrealToMeasure
  rw [← Measure.measure_univ_eq_zero, hμ]

theorem triangle_inequality (μ ν : VectorMeasure X V) [ContinuousAdd V] :
    (μ + ν).variation ≤ μ.variation + ν.variation := by
  intro s hs
  simp [variation, var_aux, hs]
  intro ι hι
  trans (∑ x ∈ ι, (‖μ x‖ₑ + ‖ν x‖ₑ))
  · apply Finset.sum_le_sum
    intro x hx
    exact enorm_add_le _ _
  · simp [Finset.sum_add_distrib]
    apply add_le_add
    · apply le_sSup; simp; use ι
      exact ciSup_const (hι := Nonempty.intro hι)
    · apply le_sSup; simp; use ι
      exact ciSup_const (hι := Nonempty.intro hι)

theorem triangle_inequality_ennrealToMeasure (μ ν : VectorMeasure X V) [ContinuousAdd V] :
    (μ + ν).variation.ennrealToMeasure ≤
    μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure := by
  rw [Measure.le_iff]
  intro s hs
  simpa [ennrealToMeasure_apply hs] using triangle_inequality μ ν s hs

theorem eq_zero_of_zero_variation_univ (μ : VectorMeasure X V) :
    μ.variation Set.univ = 0 → μ = 0 := by
  intro hμ; apply eq_zero_of_zero_variation_ennrealToMeasure_univ μ
  exact Eq.trans (ennrealToMeasure_apply (v := μ.variation) MeasurableSet.univ) hμ

theorem restrict_comm_variation (s : Set X) (μ : VectorMeasure X V) :
    (μ.restrict s).variation = μ.variation.restrict s := by
  ext t ht
  by_cases hsm : MeasurableSet s
  · simp [variation, var_aux, restrict, ht, hsm]
    apply le_antisymm
    all_goals
      apply sSup_le; intro b hb; obtain ⟨P, hP⟩ := hb
      simp [apply_ite, ← hP]; intro iP; rw [IsInnerPart] at iP; apply le_sSup
    · simp_all only [↓reduceIte]
      classical
      let Q := (P.image (fun p : Set X => p ∩ s)).erase ∅
      use Q
      have iQ : IsInnerPart (t ∩ s) Q := by
        refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
        all_goals intro q hq; simp_all [Q]; try simp only [and_comm] at hq
        all_goals obtain ⟨a, ha⟩ := hq.2; rw [← ha.1]
        · constructor;
          · trans a
            · exact inter_subset_left
            · exact (iP.1 a ha.2)
          · exact inter_subset_right
        · refine MeasurableSet.inter ?_ ?_
          · exact (iP.2.1 a ha.2)
          · exact hsm
        · intro p hp hap hap1; have := iP.2.2.1
          simp [PairwiseDisjoint] at this
          have := this ha.2 hp (by contrapose; intro f hf; rw [hf] at hap1; simp_all)
          simp_all [disjoint_iff_inter_eq_empty]; rw [← ha.1]
          exact subset_eq_empty (inter_subset_inter inter_subset_left inter_subset_left) this
      simp [ciSup_const (hι := Nonempty.intro iQ), Q]
      #check Finset.sum_erase
      #check Finset.sum_image
    · use P
      have iP : IsInnerPart t P := sorry
      simp [ciSup_const (hι := Nonempty.intro iP)]
      simp_all only [↓reduceIte]
      refine Finset.sum_congr rfl (by intro x hx; congr; apply inter_eq_self_of_subset_left; aesop)
  · simp [restrict_not_measurable μ hsm, restrict_not_measurable μ.variation hsm]

lemma variation_neg {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : VectorMeasure X E) : (-μ).variation = μ.variation := by
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
