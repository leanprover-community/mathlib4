/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
## Properties of variation
-/

open MeasureTheory BigOperators NNReal ENNReal Function Filter

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

open Classical Finset in
/-- Measure version of `le_var_aux` which was for subadditive functions. -/
lemma le_variation' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : ∀ t ∈ P, MeasurableSet t) (hP₃ : P.toSet.PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  let Q := P.filter (· ≠ ∅)
  have h : ∑ p ∈ P, ‖μ p‖ₑ = ∑ q ∈ Q, ‖μ q‖ₑ := by
    refine Eq.symm (sum_filter_of_ne fun p hp h ↦ ?_)
    by_contra! hc
    simp_all [hc]
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
  · simp [hE, μ.not_measurable' hE]
  have h : {E} ∈ {P | IsInnerPart E P} := by simpa using isInnerPart_self E hE hE'
  have := le_biSup (fun P ↦ ∑ p ∈ P, ‖μ p‖ₑ) h
  simp_all [variation, var_aux]

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
    · have h : {s} ∈ {P | IsInnerPart s P} := by simpa using isInnerPart_self s hs hc
      have := le_biSup (fun P ↦ ∑ x ∈ P, μ x) h
      simp_all
    · push_neg at hc
      simp [hc]

lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  ext _ _
  simp [variation, var_aux_zero]

-- TO DO: generalize this to the largest possible class of `VectorMeasure X V`. What are the best
-- assumptions for `V`?
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

open VectorMeasure SignedMeasure Classical in
-- TO DO: This proof can be massively improved.
lemma signedMeasure_totalVariation_le (μ : SignedMeasure X) (r : Set X) (hr : MeasurableSet r) :
    μ.totalVariation r ≤ μ.variation.ennrealToMeasure r := by
  rw [ennrealToMeasure_apply hr]
  wlog hr' : r ≠ ∅
  · simp [not_ne_iff.mp hr']
  obtain ⟨s, hsm, hs, hsc, hs', hsc'⟩ := μ.toJordanDecomposition_spec
  -- The Jordan decomposition variation is, by definition, equal to `|μ (s ∩ r)| + |μ (sᶜ ∩ r)|`.
  -- Considering the partition of `r` defined as `P := {s ∩ r, sᶜ ∩ r}` implies that it suffices
  -- to estimate `∑ p ∈ P, ‖μ p‖ₑ`. By definition this is bounded above by variation defined as a
  -- supremum.
  let P : Finset (Set X) := {s ∩ r, sᶜ ∩ r}
  have hd : Disjoint (s ∩ r) (sᶜ ∩ r) := by
    simp [Disjoint.inter_right, Set.disjoint_compl_right_iff_subset.mpr]
  have hP₁ : ∀ t ∈ P, t ⊆ r := by simp [P]
  have hP₂ : ∀ t ∈ P, MeasurableSet t := by simp [P, hsm, hr]
  have hP₃ : P.toSet.PairwiseDisjoint id := by
    -- Ridiculous case bashing, the must be a better way.
    simp only [Finset.coe_insert, Finset.coe_singleton, P]
    intro p hp q hq hpq
    obtain hc | hc : p = s ∩ r ∨ p = sᶜ ∩ r := by exact hp
    · obtain hc' | hc' : q = s ∩ r ∨ q = sᶜ ∩ r := by exact hq
      · simp_all
      · simpa [hc, hc']
    · obtain hc' | hc' : q = s ∩ r ∨ q = sᶜ ∩ r := by exact hq
      · simpa [hc, hc'] using Disjoint.symm hd
      · simp_all
  have hpos : μ.toJordanDecomposition.posPart r = ‖μ (s ∩ r)‖ₑ := by
    have : ‖μ (s ∩ r)‖ₑ = ENNReal.ofReal (μ (s ∩ r)) := by
      refine Real.enorm_of_nonneg  <| nonneg_of_zero_le_restrict μ ?_
      exact zero_le_restrict_subset μ hsm (by simp) hs
    rw [hs', this, toMeasureOfZeroLE_apply μ hs hsm hr]
    refine Eq.symm <| ofReal_eq_coe_nnreal <| nonneg_of_zero_le_restrict μ ?_
    exact zero_le_restrict_subset μ hsm Set.inter_subset_left hs
  have hneg : μ.toJordanDecomposition.negPart r = ‖μ (sᶜ ∩ r)‖ₑ := by
    have : ‖μ (sᶜ ∩ r)‖ₑ = ENNReal.ofReal (-μ (sᶜ ∩ r)) := by
      rw [show ‖μ (sᶜ ∩ r)‖ₑ = ‖-μ (sᶜ ∩ r)‖ₑ by simp]
      have : 0 ≤ -μ (sᶜ ∩ r) := by
        refine Left.nonneg_neg_iff.mpr <| nonpos_of_restrict_le_zero μ ?_
        exact restrict_le_zero_subset μ (MeasurableSet.compl_iff.mpr hsm) (by simp) hsc
      exact Real.enorm_of_nonneg this
    rw [hsc', this, toMeasureOfLEZero_apply μ hsc (MeasurableSet.compl hsm) hr]
    exact Eq.symm <| ofReal_eq_coe_nnreal _
  have hsr : s ∩ r ≠ sᶜ ∩ r := by
    by_cases hc : s ∩ r ≠ ∅
    · by_contra; simp_all
    · have : sᶜ ∩ r ≠ ∅ := by
        replace hc : Disjoint r s := by
          intro p hp hp'
          have := Set.subset_inter hp' hp
          simp_all
        rw [← Set.nonempty_iff_ne_empty] at hr' ⊢
        simpa [Set.inter_comm, ← Set.diff_eq, sdiff_eq_left.mpr hc]
      by_contra; simp_all
  have : μ.totalVariation r = ∑ p ∈ P, ‖μ p‖ₑ := by
    dsimp [totalVariation]
    rw [Finset.sum_pair hsr, hpos, hneg]
  rw [this]
  exact le_variation' μ hr hP₁ hP₂ hP₃

open VectorMeasure SignedMeasure Classical in
-- TO DO: This proof can be massively improved.
lemma le_signedMeasure_totalVariation (μ : SignedMeasure X) (r : Set X) (hr : MeasurableSet r) :
    μ.variation.ennrealToMeasure r ≤ μ.totalVariation r := by
  obtain ⟨s, hsm, hs, hsc, hs', hsc'⟩ := μ.toJordanDecomposition_spec
  -- By the Jordan decomposition, for any `p`, `|μ p| = |μ (s ∩ p) + μ (sᶜ ∩ p)|`. The positivity
  -- of each part of the decomposition and triangle inequality implies that,
  -- `|μ p| ≤ |μ (s ∩ p)| + |μ (sᶜ ∩ p)| = μ (s ∩ p) - μ (sᶜ ∩ p)`. Let `P` be a partition of `r`.
  -- To estimate variation defined as the supremum requires estimating `∑ p ∈ P, |μ p|`. Using the
  -- additivity of the measure and the above, `∑ p ∈ P, |μ p| ≤ μ (s ∩ r) - μ (sᶜ ∩ r)`.
  suffices ∀ P, IsInnerPart r P → ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.totalVariation r by
    simpa [ennrealToMeasure_apply hr, variation, var_aux, hr]
  intro P hP
  have abs_le p (hp : p ∈ P) : |μ p| ≤ μ (s ∩ p) - μ (sᶜ ∩ p) := by
    have h1 : μ p = (μ.toJordanDecomposition.posPart p).toReal -
        (μ.toJordanDecomposition.negPart p).toReal := by
      nth_rw 1 [← toSignedMeasure_toJordanDecomposition μ]
      simp only [JordanDecomposition.toSignedMeasure, coe_sub, Pi.sub_apply,
        Measure.toSignedMeasure_apply, hP.2.1 p hp, reduceIte]
      exact rfl
    have h2 : (μ.toJordanDecomposition.posPart p).toReal = μ (s ∩ p) := by
      simp [hs', toMeasureOfZeroLE_apply μ hs hsm (hP.2.1 p hp)]
    have h3 : (μ.toJordanDecomposition.negPart p).toReal = - μ (sᶜ ∩ p) := by
      simp [hsc', toMeasureOfLEZero_apply μ hsc (MeasurableSet.compl hsm) (hP.2.1 p hp)]
    rw [h1, h2, h3]
    have h5 : μ (s ∩ p) = |μ (s ∩ p)| := by
      refine Eq.symm <| abs_of_nonneg <| nonneg_of_zero_le_restrict μ ?_
      exact zero_le_restrict_subset μ hsm (by simp) hs
    have h6 : μ (sᶜ ∩ p) = - |μ (sᶜ ∩ p)| := by
      have h : μ (sᶜ ∩ p) ≤ 0 := by
        refine nonpos_of_restrict_le_zero μ ?_
        exact restrict_le_zero_subset μ (MeasurableSet.compl_iff.mpr hsm) (by simp) hsc
      simp [abs_of_nonpos h]
    nth_rw 2 [h5, h6]
    simpa using abs_add_le (μ (s ∩ p)) (μ (sᶜ ∩ p))
  suffices (∑ p ∈ P, ‖μ p‖ₑ).toReal ≤ (μ.totalVariation r).toReal by
    refine (toNNReal_le_toNNReal ?_ ?_).mp this
    · exact sum_ne_top.mpr <| fun _ _ ↦  enorm_ne_top
    · exact Finiteness.add_ne_top (measure_ne_top μ.toJordanDecomposition.posPart r)
        (measure_ne_top μ.toJordanDecomposition.negPart r)
  -- Extract the essential logic of the following two haves: subadditivity of the measure if nonneg.
  have : ∑ p ∈ P, μ (s ∩ p) ≤ μ (s ∩ r) := calc
    _ = μ (⋃ p ∈ P, (s ∩ p)) := by
      have : ⋃ p ∈ P, (s ∩ p) = ⋃ i : P, (s ∩ i.val) := by apply Set.biUnion_eq_iUnion
      rw [this, μ.of_disjoint_iUnion]
      · rw [← Finset.tsum_subtype]
      · rw [Subtype.forall]
        intro p hp
        exact MeasurableSet.inter hsm <| hP.2.1 p hp
      · intro p q h
        have hd := hP.2.2.1 p.property q.property (Subtype.coe_ne_coe.mpr h)
        intro x hxp hxq
        have hxpq : x ⊆ p ∩ q := by
          simp only [Set.le_eq_subset, Set.subset_inter_iff] at hxp hxq
          exact Set.subset_inter hxp.2 hxq.2
        exact le_of_le_of_eq hxpq <| Disjoint.inter_eq hd
    _ = μ (s ∩ (⋃ p ∈ P, p)) := by
      congr
      exact Eq.symm (Set.inter_iUnion₂ s fun i j ↦ i)
    _ ≤ μ (s ∩ r) := by
      have : μ (s ∩ r) = μ (s ∩ ⋃ p ∈ P, p) + μ ((s ∩ r) \ (s ∩ ⋃ p ∈ P, p)) := by
        refine Eq.symm (of_add_of_diff ?_ ?_ ?_)
        · exact MeasurableSet.inter hsm <| Finset.measurableSet_biUnion P hP.2.1
        · exact MeasurableSet.inter hsm hr
        · exact Set.inter_subset_inter_right _ <| Set.iUnion₂_subset_iff.mpr hP.1
      simp only [this, le_add_iff_nonneg_right, ge_iff_le]
      refine nonneg_of_zero_le_restrict μ <| zero_le_restrict_subset μ hsm ?_ hs
      exact subset_trans Set.diff_subset (Set.inter_subset_left : s ∩ r ⊆ s)
  have : μ (sᶜ ∩ r) ≤ ∑ p ∈ P, μ (sᶜ ∩ p) := calc
    _ ≤ μ (sᶜ ∩ (⋃ p ∈ P, p)) := by
      have : μ (sᶜ ∩ r) = μ (sᶜ ∩ ⋃ p ∈ P, p) + μ ((sᶜ ∩ r) \ (sᶜ ∩ ⋃ p ∈ P, p)) := by
        refine Eq.symm (of_add_of_diff ?_ ?_ ?_)
        · refine MeasurableSet.inter ?_ ?_
          exact MeasurableSet.compl_iff.mpr hsm
          refine Finset.measurableSet_biUnion P hP.2.1
        · exact MeasurableSet.inter (MeasurableSet.compl_iff.mpr hsm) hr
        · apply Set.inter_subset_inter_right
          exact Set.iUnion₂_subset_iff.mpr hP.1
      rw [this]
      rw [add_le_iff_nonpos_right]
      refine nonpos_of_restrict_le_zero μ ?_
      have : (sᶜ ∩ r) \ (sᶜ ∩ ⋃ p ∈ P, p) ⊆ sᶜ := by
        refine subset_trans ?_ (Set.inter_subset_left : sᶜ ∩ r ⊆ sᶜ)
        exact Set.diff_subset
      refine restrict_le_zero_subset μ (MeasurableSet.compl_iff.mpr hsm) this hsc
    _ = μ (⋃ p ∈ P, (sᶜ ∩ p)) := by
      congr
      exact Set.inter_iUnion₂ sᶜ fun i j ↦ i
    _ = ∑ p ∈ P, μ (sᶜ ∩ p) := by
      have : ⋃ p ∈ P, (sᶜ ∩ p) = ⋃ i : P, (sᶜ ∩ i.val) := by apply Set.biUnion_eq_iUnion
      rw [this, μ.of_disjoint_iUnion]
      · rw [← Finset.tsum_subtype]
      · rw [Subtype.forall]
        intro p hp
        exact MeasurableSet.inter (MeasurableSet.compl_iff.mpr hsm) (hP.2.1 p hp)
      · intro p q h x hxp hxq
        have hd := hP.2.2.1 p.property q.property (Subtype.coe_ne_coe.mpr h)
        simp only [Set.le_eq_subset, Set.subset_inter_iff] at hxp hxq
        have hxpq : x ⊆ p.val ∩ q.val := by
          exact Set.subset_inter hxp.2 hxq.2
        exact le_of_le_of_eq hxpq <| Disjoint.inter_eq hd
  calc (∑ p ∈ P, ‖μ p‖ₑ).toReal
    _ = ∑ p ∈ P, (‖μ p‖ₑ).toReal := by
      simp [toReal_sum]
    _ = ∑ p ∈ P, |μ p| := by
      simp [Finset.sum_congr]
    _ ≤ ∑ p ∈ P, (μ (s ∩ p) - μ (sᶜ ∩ p)) := by
      gcongr with p hp
      exact abs_le p hp
    _ = ∑ p ∈ P, μ (s ∩ p) - ∑ p ∈ P, μ (sᶜ ∩ p) :=
      Finset.sum_sub_distrib
    _ ≤ μ (s ∩ r) - μ (sᶜ ∩ r) := by
      gcongr
    _ = (μ.totalVariation r).toReal := by
      have h' : μ (s ∩ r) = (μ.toJordanDecomposition.posPart r).toReal := by
        simp [hs', toMeasureOfZeroLE_apply μ hs hsm hr]
      have h'' : μ (sᶜ ∩ r) = - (μ.toJordanDecomposition.negPart r).toReal := by
        simp [hsc', toMeasureOfLEZero_apply μ hsc (MeasurableSet.compl hsm) hr]
      simp [totalVariation, h', h'', toReal_add, measure_ne_top μ.toJordanDecomposition.posPart r,
        measure_ne_top μ.toJordanDecomposition.negPart r]

open VectorMeasure SignedMeasure in
/-- For signed measures, variation defined by the Hahn–Jordan decomposition coincides with variation
defined as a sup. -/
lemma signedMeasure_totalVariation_eq (μ : SignedMeasure X) :
    totalVariation μ = μ.variation.ennrealToMeasure := by
  ext r hr
  refine eq_of_le_of_le ?_ ?_
  · exact signedMeasure_totalVariation_le μ r hr
  · exact le_signedMeasure_totalVariation μ r hr

end MeasureTheory.VectorMeasure
