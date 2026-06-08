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

open scoped ENNReal Function Topology
open Set Filter

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
  exact (ContinuousLinearMap.le_opNorm_enorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

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

lemma _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_of_lt_variation
    (μ : SignedMeasure X) (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.variation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  simp_rw [two_mul]
  obtain ⟨P, Ps, P_disj, P_meas, hP⟩ : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧
    ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (∀ t ∈ P, MeasurableSet t) ∧ a < ∑ p ∈ P, ‖μ p‖ₑ := exists_lt_sum_of_lt_variation _ hs ha
  have I : (∑ p ∈ P.filter (fun p ↦ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ := by
    simp only [Real.norm_eq_abs, enorm_eq_nnnorm,
      ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_inj, ← NNReal.coe_inj,
      NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with 0 ≤ μ x, |μ x| = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := calc
      _ = ∑ x ∈ P with 0 ≤ μ x, μ x := by
        apply Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp]
      _ = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := by
        rw [of_biUnion_finset]
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonneg]
    rw [← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  have J : (∑ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ := by
    simp only [not_le, enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_inj, ← NNReal.coe_inj, NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with μ x < 0, |μ x| = - μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := calc
      ∑ x ∈ P with μ x < 0, |μ x|
      _ = ∑ x ∈ P with μ x < 0, -μ x := by
        refine Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp.2.le]
      _ = -μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := by
        rw [of_biUnion_finset]
        · simp
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonpos]
    rw [← neg_nonneg, ← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p ↦ 0 ≤ μ p), I, J] at hP
  rcases le_total (‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ)
    (‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ) with h | h
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)

lemma exists_subset_lt_enorm_of_lt_semiVariation (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.semiVariation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : ∃ ℓ ∈ {ℓ : StrongDual ℝ E| ‖ℓ‖ₑ ≤ 1},
    a < (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opNorm_enorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

lemma foot (hs : MeasurableSet s) (h's : μ.semiVariation s = ∞) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semiVariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ := by
  obtain ⟨t, ts, t_meas, ht⟩ : ∃ t ⊆ s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_of_lt_semiVariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ ≤ ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add, add_comm, mul_one]
    exact ht.le
  have I : ∞ ≤ μ.semiVariation t + μ.semiVariation (s \ t) := by
    rw [← h's]
    apply le_trans (semiVariation_mono (by simp)) semiVariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ ≤ ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_diff t_meas hs ts]; abel
      rw [this, add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, diff_subset, hI, ?_⟩
    simp only [sdiff_sdiff_right_self, Set.le_eq_subset, ts, inf_of_le_right]
    exact le_trans (by simp) h't

lemma bar : μ.semiVariation univ < ∞ := by
  apply Ne.lt_top (fun h ↦ ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semiVariation s = ∞) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semiVariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ := foot hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semiVariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 ≤ ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n ↦ ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn ↦ ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, le_eq_subset, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n ↦ (hs n).1.diff (hs (n + 1)).1) u_disj
  have := this.summable.tendsto_atTop_zero
  have := tendsto_zero_iff_enorm





#exit

hasSum_of_disjoint_iUnion (hm : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :





end MeasureTheory.VectorMeasure
