/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker, Arav Bhattacharyya
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Tight sets of measures

A set of measures is tight if for all `0 < ε`, there exists a compact set `K` such that for all
measures in the set, the complement of `K` has measure at most `ε`.

## Main definitions

* `MeasureTheory.IsTightMeasureSet`: A set of measures `S` is tight if for all `0 < ε`, there exists
  a compact set `K` such that for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `⨆ μ ∈ S, μ` tends to `0` along the
  filter of cocompact sets.
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` establishes equivalence between
  the two definitions.

## Main statements

* `isTightMeasureSet_singleton_of_innerRegularWRT`: every finite, inner-regular measure is tight.
* `isTightMeasureSet_of_isCompact_closure`: every relatively compact set of measures is tight.


-/

@[expose] public section

open Filter Set Metric ENNReal NNReal MeasureTheory ProbabilityMeasure TopologicalSpace

open scoped ENNReal NNReal Topology FiniteMeasure ProbabilityMeasure

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {S T : Set (Measure 𝓧)}

section Basic

variable [TopologicalSpace 𝓧]

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the definition above
in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
def IsTightMeasureSet (S : Set (Measure 𝓧)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact 𝓧).smallSets (𝓝 0)

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`. -/
lemma isTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set 𝓧, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
    exact ⟨K, h1, hA Kᶜ h2⟩
  · obtain ⟨K, h1, h2⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS ↦ (μ.mono hA).trans (h2 μ hμS)⟩

@[deprecated (since := "2025-12-13")] alias
IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :=
isTightMeasureSet_iff_exists_isCompact_measure_compl_le

/-- Finite measures that are inner regular with respect to closed compact sets are tight. -/
theorem isTightMeasureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ]
    (h : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet) :
    IsTightMeasureSet {μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hεr.ne_bot hε.ne'
    obtain ⟨K, _, ⟨hK_compact, hK_closed⟩, hKμ⟩ := h .univ (r - ε) hεr'
    refine ⟨K, hK_compact, ?_⟩
    simp only [mem_singleton_iff, forall_eq]
    rw [measure_compl hK_closed.measurableSet (measure_ne_top μ _), tsub_le_iff_right]
    rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
    exact hKμ.le
  | inr hεr => exact ⟨∅, isCompact_empty, by simpa⟩

/-- Inner regular finite measures on T2 spaces are tight. -/
lemma isTightMeasureSet_singleton_of_innerRegular [T2Space 𝓧] [OpensMeasurableSpace 𝓧]
    [IsFiniteMeasure μ] [h : μ.InnerRegular] :
    IsTightMeasureSet {μ} := by
  refine isTightMeasureSet_singleton_of_innerRegularWRT ?_
  intro s hs r hr
  obtain ⟨K, hKs, hK_compact, hμK⟩ := h.innerRegular hs r hr
  exact ⟨K, hKs, ⟨hK_compact, hK_compact.isClosed⟩, hμK⟩

/-- In a complete second-countable pseudo-metric space, finite measures are tight. -/
theorem isTightMeasureSet_singleton {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

namespace IsTightMeasureSet

/-- In a compact space, every set of measures is tight. -/
lemma of_compactSpace [CompactSpace 𝓧] : IsTightMeasureSet S := by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ ↦ mem_of_mem_nhds

protected lemma subset (hT : IsTightMeasureSet T) (hST : S ⊆ T) :
    IsTightMeasureSet S :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ ↦ by simp)
    (iSup_le_iSup_of_subset hST)

protected lemma union (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet (S ∪ T) := by
  rw [IsTightMeasureSet, iSup_union]
  convert Tendsto.sup_nhds hS hT
  simp

protected lemma inter (hS : IsTightMeasureSet S) (T : Set (Measure 𝓧)) :
    IsTightMeasureSet (S ∩ T) :=
  hS.subset inter_subset_left

lemma map [TopologicalSpace 𝓨] [MeasurableSpace 𝓨] [OpensMeasurableSpace 𝓨] [T2Space 𝓨]
    (hS : IsTightMeasureSet S) {f : 𝓧 → 𝓨} (hf : Continuous f) :
    IsTightMeasureSet (Measure.map f '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro ε hε
  obtain ⟨K, hK_compact, hKS⟩ := hS ε hε
  refine ⟨f '' K, hK_compact.image hf, fun μ hμS ↦ ?_⟩
  by_cases hf_meas : AEMeasurable f μ
  swap; · simp [Measure.map_of_not_aemeasurable hf_meas]
  rw [Measure.map_apply_of_aemeasurable hf_meas (hK_compact.image hf).measurableSet.compl]
  refine (measure_mono ?_).trans (hKS μ hμS)
  simp only [preimage_compl, compl_subset_compl]
  exact subset_preimage_image f K

end IsTightMeasureSet
end Basic

variable [PseudoMetricSpace 𝓧] [OpensMeasurableSpace 𝓧] [SecondCountableTopology 𝓧]
  {S : Set (ProbabilityMeasure 𝓧)}

lemma exists_measure_iUnion_gt_of_isCompact_closure
    (U : ℕ → Set 𝓧) (O : ∀ i, IsOpen (U i)) (Cov : ⋃ i, U i = univ) (hcomp : IsCompact (closure S))
    (ε : ℝ≥0∞) (hε : 0 < ε) (hεbound : ε ≤ 1) :
    ∃ (k : ℕ), ∀ μ ∈ S, 1 - ε < μ (⋃ i ≤ k, U i) := by
  have εfin : ε ≠ ∞ := ne_top_of_le_ne_top (by simp) hεbound
  lift ε to ℝ≥0 using εfin
  obtain ⟨ε, hε', rfl⟩ : ∃ (ε' : ℝ) (hε' : 0 ≤ ε'), ε = .mk ε' hε' := ⟨↑ε, ε.2, rfl⟩
  simp only [ENNReal.coe_pos, ← NNReal.coe_lt_coe, NNReal.coe_zero, coe_mk, coe_le_one_iff,
      ← NNReal.coe_le_coe, NNReal.coe_one] at hε hεbound
  by_contra! nh
  choose μ hμInS hcontradiction using nh
  obtain ⟨μlim, _, sub, hsubmono, hμconverges⟩ :=
      hcomp.isSeqCompact (fun n ↦ subset_closure <| hμInS n)
  have Measurebound n : (μlim (⋃ (i ≤ n), U i) : ℝ) ≤ 1 - ε := calc
    (μlim (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := isOpen_biUnion fun i a ↦ O i
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμconverges hopen
      simp_rw [Function.comp_apply, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [← ofNNReal_liminf] at this
      · exact mod_cast this
      use 1
      simpa [ge_iff_le, eventually_map, eventually_atTop, forall_exists_index] using fun _ x h ↦
          (h x (by simp)).trans <| ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop, ge_iff_le]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono
            <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        exact le_trans (Nat.le_add_right n 1) (le_trans hypo (StrictMono.le_apply hsubmono))
      · use 0; simp
      · use 1
        simpa [ge_iff_le, eventually_map, eventually_atTop, ge_iff_le, forall_exists_index] using
            fun _ d hyp ↦ (hyp d (by simp)).trans (by simp)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0; simp
      simp only [eventually_atTop, ge_iff_le, forall_exists_index]
      intro b c h
      apply le_trans (h c le_rfl)
      refine (ofReal_le_ofReal_iff (by rw [sub_nonneg]; exact hεbound)).mp ?_
      rw [ofReal_coe_nnreal]
      apply le_trans (hcontradiction (sub c))
      norm_cast
  have accumulation : Tendsto (fun n ↦ μlim (⋃ i ≤ n, U i)) atTop (𝓝 (μlim (⋃ i, U i))) := by
    simp_rw [← Set.accumulate_def, ProbabilityMeasure.tendsto_measure_iUnion_accumulate]
  rw [Cov, coeFn_univ, ← NNReal.tendsto_coe] at accumulation
  have exceeds_bound : ∀ᶠ n in atTop, (1 - ε / 2 : ℝ) ≤ μlim (⋃ i ≤ n, U i) :=
      Tendsto.eventually_const_le (v := 1)
        (by simp only [sub_lt_self_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right]; positivity)
        accumulation
  suffices ∀ᶠ n : ℕ in atTop, False from this.exists.choose_spec
  filter_upwards [exceeds_bound] with n hn
  linarith [hn.trans <| Measurebound n]

variable [CompleteSpace 𝓧]

/-- In a second countable complete metric space, a set of probability measures with compact closure
is tight. -/
theorem isTightMeasureSet_of_isCompact_closure (hcomp : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure 𝓧) : Measure 𝓧) | μ ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  rcases isEmpty_or_nonempty 𝓧 with hempty | hnonempty
  · rw [← univ_eq_empty_iff] at hempty
    exact fun ε εpos ↦ ⟨∅, isCompact_empty, by simp [hempty]⟩
  obtain ⟨D, hD⟩ := exists_dense_seq 𝓧
  obtain ⟨u, hu_anti, hu_pos, hu⟩ : ∃ u, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have hcov (m : ℕ) : ⋃ i, ball (D i) (u m) = univ := by
    rw [denseRange_iff] at hD
    ext p
    exact ⟨fun a ↦ trivial, fun _ ↦ mem_iUnion.mpr <| hD p (u m) (hu_pos m)⟩
  intro ε εpos
  rcases lt_or_ge 1 ε with hεbound | hεbound
  · refine ⟨∅, isCompact_empty, fun μ hμ ↦ ?_⟩
    simp only [mem_setOf_eq] at hμ
    obtain ⟨μ', hμ', rfl⟩ := hμ
    rw [compl_empty, measure_univ]
    exact le_of_lt hεbound
  have byclaim (m : ℕ) : ∃ k, ∀ μ ∈ S, 1 - (ε * 2 ^ (-m : ℤ) : ℝ≥0∞) <
      μ (⋃ i ≤ k, ball (D i) (u m)) := by
    refine exists_measure_iUnion_gt_of_isCompact_closure
      (fun i ↦ ball (D i) (u m)) (fun _ ↦ isOpen_ball) (hcov m) hcomp (ε * 2 ^ (-m : ℤ)) ?_ ?_
    · simpa using ⟨εpos, (ENNReal.zpow_pos (by simp) (by simp) (-↑m))⟩
    · exact Left.mul_le_one hεbound <| zpow_le_one_of_nonpos (by linarith) (by simp)
  choose! km hbound using byclaim
  -- This is a set we can construct to show tightness
  let bigK := ⋂ m, ⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m))
  have bigcalc (μ : ProbabilityMeasure 𝓧) (hs : μ ∈ S) : μ.toMeasure bigKᶜ ≤ ε := calc
    μ.toMeasure bigKᶜ
    _ = μ.toMeasure (⋃ m, (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))ᶜ) := by simp [bigK]
    _ ≤ ∑' m, μ.toMeasure (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))ᶜ :=
      measure_iUnion_le _
    _ = ∑' m, (1 - μ.toMeasure (⋃ (i ≤ km (m + 1)), closure (ball (D i) (u m)))) := by
      congr! with m; rw [measure_compl (by measurability) (by simp)]; simp
    _ ≤ (∑' (m : ℕ), (ε : ℝ≥0∞) * 2 ^ (-(m + 1) : ℤ)) := by
      refine tsum_le_tsum fun m ↦ tsub_le_iff_tsub_le.mp ?_
      replace hbound := (hbound (m + 1) μ hs).le
      simp_all only [neg_add_rev, Int.reduceNeg, tsub_le_iff_right, Nat.cast_add, Nat.cast_one,
          ← coe_ofNat, ← ennreal_coeFn_eq_coeFn_toMeasure]
      grw [hbound]
      gcongr with i hi
      grw [← subset_closure (s := ball (D i) (u m)), ball_subset_ball]
      exact hu_anti.antitone (by grind)
    _ = ε := by
      rw [ENNReal.tsum_mul_left]
      nth_rw 2 [← mul_one (a := ε)]
      congr
      ring_nf
      exact tsum_two_zpow_neg_add_one
  -- Final proof
  refine ⟨bigK, ?_, by simpa⟩
  -- Compactness first
  refine TotallyBounded.isCompact_of_isClosed ?_ ?_
  --Totally bounded
  · refine Metric.totallyBounded_iff.mpr fun δ δpos ↦ ?_
    have ⟨δ_inv, hδ_inv⟩ : ∃ x, u x < δ := (Tendsto.eventually_lt_const δpos hu).exists
    refine ⟨D '' .Iic (km (δ_inv + 1)), (Set.finite_Iic _).image _, ?_⟩
    -- t should be image under D of the set of numbers less than km of δ_inv
    simp only [mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, bigK]
    calc
        ⋂ m, ⋃ i ≤ km (m + 1), closure (ball (D i) (u m))
    _ ⊆ ⋃ i ≤ km (δ_inv + 1), closure (ball (D i) (u δ_inv)) := iInter_subset ..
    _ ⊆ ⋃ i ≤ km (δ_inv + 1), ball (D i) δ := by
        gcongr
        exact closure_ball_subset_closedBall.trans <| closedBall_subset_ball <| hδ_inv
  -- Closedness
  · simp_rw [bigK, ← Set.mem_Iic]
    exact isClosed_iInter fun n =>
      Finite.isClosed_biUnion (finite_Iic _) (fun _ _ ↦ isClosed_closure)


end MeasureTheory
