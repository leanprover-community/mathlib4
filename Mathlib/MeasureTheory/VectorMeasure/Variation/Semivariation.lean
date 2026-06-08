/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The semivariation of a vector measure

-/

public section

open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mX : MeasurableSpace X}
  {μ : VectorMeasure X E} {s t : Set X}

/-- The semivariation of a vector measure, defined as the supremum of the variations
of the images of the vector measures under continuous linear forms of norm at most `1`. -/
noncomputable def semiVariation (μ : VectorMeasure X E) (s : Set X) : ℝ≥0∞ :=
  ⨆ ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1}, (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s

lemma semiVariation_union_le :
    μ.semiVariation (s ∪ t) ≤ μ.semiVariation s + μ.semiVariation t := by
  simp only [semiVariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ

lemma semiVariation_mono (hst : s ⊆ t) : μ.semiVariation s ≤ μ.semiVariation t := by
  simp only [semiVariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

lemma semiVariation_le_variation : μ.semiVariation s ≤ μ.variation s := by
  simp only [semiVariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation ≤ μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  exact mul_le_of_le_one_left (by positivity) hℓ

lemma enorm_measure_le_semiVariation : ‖μ s‖ₑ ≤ μ.semiVariation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : ∃ ℓ : StrongDual ℝ E, ‖ℓ‖ ≤ 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ ≤ (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ ≤ μ.semiVariation s := by apply le_biSup _ h'ℓ

lemma enorm_measure_le_semiVariation_of_subset (hst : s ⊆ t) :
    ‖μ s‖ₑ ≤ μ.semiVariation t :=
  enorm_measure_le_semiVariation.trans (semiVariation_mono hst)

lemma foot (μ : VectorMeasure X ℝ) (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (h's : μ.variation s ≠ ∞) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ.variation s - ε ≤ 2 * ‖μ t‖ₑ := by
  obtain ⟨P, Ps, P_disj, P_meas, hP⟩ : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧
      ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε :=
    exists_variation_le_add' _ hs hε.bot_lt h's
  have A (p) : ∃ (f : ℝ), (f = 1 ∨ f = -1) ∧ ‖μ p‖ = f * μ p := by
    rcases le_total (μ p) 0 with h'p | h'p
    · exact ⟨-1, by simp [h'p]⟩
    · exact ⟨1, by simp [h'p]⟩
  choose f hf h'f using A


#exit

lemma exists_variation_le_add' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hμ : μ.variation s ≠ ∞) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε := by


lemma exists_semiVariation_le_enorm_measure (ε : ℝ≥0∞) (hε : ε ≠ 0) (htop : μ.semiVariation t ≠ ∞) :
    ∃ s ⊆ t, MeasurableSet s ∧ μ.semiVariation t ≤ 2 * ‖μ s‖ₑ + ε := by
  rcases eq_zero_or_pos (μ.semiVariation t) with ht | ht
  · refine ⟨∅, by simp [ht]⟩
  obtain ⟨ℓ, ℓmem, hℓ⟩ : ∃ ℓ ∈ {ℓ : StrongDual ℝ E| ‖ℓ‖ₑ ≤ 1},
      μ.semiVariation t - ε < (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation t :=
    lt_biSup_iff.1 (ENNReal.sub_lt_self htop ht.ne' hε)



#exit

theorem exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
    (hε : ε ≠ 0) : ∃ K, K ⊆ U ∧ p K ∧ μ U < μ K + ε := by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩



end MeasureTheory.VectorMeasure
