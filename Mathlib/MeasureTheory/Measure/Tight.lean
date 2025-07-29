/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

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
* `IsTight_of_isRelativelyCompact`: every relatively compact set of measures is tight.

-/

open Filter Set

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} [TopologicalSpace 𝓧] {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} {S T : Set (Measure 𝓧)}

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the definition above
in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
def IsTightMeasureSet (S : Set (Measure 𝓧)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact 𝓧).smallSets (𝓝 0)

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`. -/
lemma IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set 𝓧, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
    exact ⟨K, h1, hA Kᶜ h2⟩
  · obtain ⟨K, h1, h2⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS ↦ (μ.mono hA).trans (h2 μ hμS)⟩

/-- Finite measures that are inner regular with respect to closed compact sets are tight. -/
theorem isTightMeasureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ]
    (h : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet) :
    IsTightMeasureSet {μ} := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) (zero_le'.trans_lt hεr).ne'
      hε.ne'
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
theorem isTightMeasureSet_singleton {α : Type*} {mα : MeasurableSpace α}
    [PseudoEMetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
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
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
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


open Metric ENNReal NNReal ProbabilityMeasure TopologicalSpace

variable {X : Type*} [MeasurableSpace X]

--omit [TopologicalSpace X] in
lemma ENNreal_ProbMeasure_toMeasure (μ : ProbabilityMeasure X) (A : Set X) :
    μ.toMeasure A = ((μ A) : ENNReal) := by
    exact Eq.symm (ennreal_coeFn_eq_coeFn_toMeasure μ A)

variable [PseudoMetricSpace X] -- Could probably generalize to PseudoEMetricSpace

variable (S : Set (ProbabilityMeasure X))

lemma lt_geom_series (D : ℕ → X) (ε : ℝ≥0∞) (μ : ProbabilityMeasure X) (hs : μ ∈ S) (km : ℕ → ℕ)
    (hbound : ∀ k : ℕ, ∀ μ ∈ S, (μ (⋃ i, ⋃ (_ : i ≤ km k), ball (D i) (1 / (↑k + 1)))) >
    1 - ε * 2 ^ (-k : ℤ)) :
  ∑' (m : ℕ), (1 - μ.toMeasure (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))) ≤
  ∑' (m : ℕ), (ε: ENNReal) * 2 ^ (-((m:ℤ) + 1)) := by
  refine ENNReal.tsum_le_tsum ?_
  intro m
  specialize hbound (m+1) μ hs
  refine tsub_le_iff_tsub_le.mp ?_
  apply le_of_lt at hbound
  simp only [neg_add_rev, Int.reduceNeg, one_div, tsub_le_iff_right]
  simp only [Nat.cast_add, Nat.cast_one, one_div, tsub_le_iff_right] at hbound
  rw [← ENNReal.coe_ofNat,← ENNReal.coe_zpow,ENNreal_ProbMeasure_toMeasure]
  swap; · simp
  apply le_trans hbound
  gcongr
  · refine apply_mono μ <| iUnion₂_mono ?_
    intro i hi
    rw [subset_def]
    intro x hx; rw [EMetric.mem_closure_iff_infEdist_zero]
    refine EMetric.infEdist_zero_of_mem ?_
    rw [mem_ball']; rw [mem_ball'] at hx;
    apply hx.trans; field_simp
    refine (one_div_lt_one_div (by positivity) (by positivity)).mpr (by simp)
  · rw [← Int.neg_add, zpow_neg]; norm_cast
    simp only [zpow_negSucc, Nat.cast_pow, Nat.cast_ofNat, ne_eq, Nat.add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, coe_inv,
      ENNReal.coe_pow, coe_ofNat, ENNReal.inv_le_inv]
    rw [Nat.add_comm m 1]

variable [OpensMeasurableSpace X]

noncomputable section

variable [SeparableSpace X]

lemma MeasOpenCoverTendstoMeasUniv (U : ℕ → Set X) (O : ∀ i, IsOpen (U i))
    (hcomp : IsCompact (closure S)) (ε : ℝ≥0∞) (hε : ε > 0) (hεbound : ε ≤ 1)
    (Cov : ⋃ i, U i = univ) : ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh; choose μ hμInS hcontradiction using nh
  obtain ⟨μlim, _, sub, hsubmono, hμconverges⟩ :=
  hcomp.isSeqCompact (fun n ↦ subset_closure <| hμInS n)
  have Measurebound n := calc
    (μlim (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := by
        exact isOpen_biUnion fun i a ↦ O i
      --This is the key lemma
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμconverges hopen
      simp only [Function.comp_apply] at this
      rw [toReal_liminf]; norm_cast
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this; norm_cast at this
      use 1
      simp only [ge_iff_le, eventually_map, eventually_atTop, forall_exists_index]
      intro a x h
      specialize h x (by simp); apply h.trans
      exact ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop, ge_iff_le]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono
        <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        exact le_trans (Nat.le_add_right n 1) (le_trans hypo (StrictMono.le_apply hsubmono))
      · simp only [autoParam, ge_iff_le, isBoundedUnder_ge_toReal]
        use 0; simp
      · simp only [autoParam, ge_iff_le, isCoboundedUnder_ge_toReal]
        use 1; simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
        intro a d hyp
        specialize hyp d (by simp)
        apply hyp.trans; norm_cast
        exact ProbabilityMeasure.apply_le_one (μ (sub d)) (⋃ i ≤ sub d, U i)
    _ ≤ (1 - (ε.toReal) : ℝ) := by
      apply Filter.liminf_le_of_le
      · use 0; simp
      simp only [eventually_atTop, ge_iff_le, forall_exists_index]
      intro b c h
      apply le_trans (h c le_rfl)
      refine (ofReal_le_ofReal_iff ?_).mp ?_
      · rw [sub_nonneg]
        exact toReal_le_of_le_ofReal (zero_le_one' ℝ) (by rw [ofReal_one]; exact hεbound)
      rw [ofReal_coe_nnreal]
      apply le_trans (hcontradiction (sub c))
      rw [← ofReal_one, ENNReal.ENNReal_ofReal_one_sub_ENNReal_toReal_eq];
      refine le_of_eq ?_
      norm_cast; exact hεbound
  have accumulation : Tendsto (fun n ↦ μlim (⋃ i ≤ n, U i)) atTop (𝓝 (μlim (⋃ i, U i))) := by
    simp_rw [←Set.accumulate_def]
    exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
  rw [Cov, coeFn_univ, ←NNReal.tendsto_coe] at accumulation
  have exceeds_bound : ∀ᶠ n in atTop, μlim (⋃ i ≤ n, U i) ≥ 1 - ε / 2 :=
    Tendsto.eventually_const_le (v := 1) (((ENNReal.sub_lt_self_iff (one_ne_top)).mpr
    ⟨zero_lt_one' ℝ≥0∞, ENNReal.half_pos <| pos_iff_ne_zero.mp hε⟩))
    ((tendsto_toReal_iff (by simp) (by simp)).mp accumulation)
  suffices ∀ᶠ n : ℕ in atTop, False by exact this.exists.choose_spec
  filter_upwards [exceeds_bound] with n hn
  have Measurebound := Measurebound n
  have booosh : ((μlim (⋃ i, ⋃ (_ : i ≤ n), U i)) : ℝ) ≥ (1 - ε / 2).toReal := by
    exact toReal_le_coe_of_le_coe hn
  have := booosh.trans Measurebound
  rw [one_sub_ENNReal_toReal_eq ε hεbound] at this
  simp only [ne_eq, sub_eq_top_iff, one_ne_top, false_and,
   not_false_eq_true, toReal_le_toReal] at this
  have εfin : ε ≠ ⊤ := by
    intro h; rw [h] at hεbound
    exact not_top_le_coe hεbound
  have half_lt : ε / 2 < ε := ENNReal.half_lt_self (pos_iff_ne_zero.mp hε) εfin
  have half_gt : ε / 2 ≥ ε := by
    rw [tsub_le_iff_tsub_le,
      Eq.symm (ENNReal.eq_sub_of_add_eq' one_ne_top (add_tsub_cancel_of_le hεbound))] at this
    exact this
  exact not_le.mpr half_lt half_gt




variable [CompleteSpace X]

lemma mul_shifted_geom_series (ε : ENNReal) : (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ)) = ε := by
  rw [ENNReal.tsum_mul_left]
  nth_rw 2 [←mul_one (a :=ε)]; congr; simp_rw [← Nat.cast_one (R := ℤ), ← Nat.cast_add,
  ENNReal.zpow_neg (x:= 2) (by norm_num) (by norm_num), zpow_natCast,
  ENNReal.inv_pow, ENNReal.tsum_geometric_add_one]
  norm_num; rw [ENNReal.inv_mul_cancel]; all_goals norm_num

lemma NNReal_pow_le_one (m : ℤ) (n : NNReal) (hn : 1 ≤ n) (hm : m ≤ 0) :
    (n ^ m : ENNReal) ≤ 1 := by
  convert_to (n ^ (m : ℝ) : ENNReal) ≤ 1
  · simp
  rw [← coe_rpow_of_ne_zero (by positivity)]; simp only [NNReal.rpow_intCast, coe_le_one_iff]
  exact zpow_le_one_of_nonpos₀ hn hm

theorem IsTight_of_isRelativelyCompact (hcomp : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  by_cases hempty : IsEmpty X
  · intro ε εpos; use ∅; constructor
    · exact isCompact_empty
    intro μ hμ
    rw [← univ_eq_empty_iff] at hempty
    rw [←hempty]
    simp
  simp only [not_isEmpty_iff] at hempty
  intro ε εpos
  obtain ⟨D, hD⟩ := exists_dense_seq X
  have hcov (m : ℕ): ⋃ i, ball (D i) (1 / (m+1)) = univ := by
    rw [denseRange_iff] at hD; ext p
    exact ⟨fun a ↦ trivial,fun _ ↦ mem_iUnion.mpr <| hD p (1 / (m+1)) Nat.one_div_pos_of_nat⟩
  by_cases hεbound : ε > 1
  · use ∅
    constructor;
    · exact isCompact_empty
    intro μ hμ
    simp only [mem_setOf_eq] at hμ
    obtain ⟨μ', hμ', rfl⟩ := hμ
    rw [compl_empty,measure_univ]; exact le_of_lt hεbound
  have byclaim (m : ℕ) : ∃ (k : ℕ),∀ μ ∈ S, μ (⋃ i ≤ k, ball (D i) (1 / (m+1))) >
  1 - (ε * 2 ^ (- m : ℤ) : ℝ≥0∞) := by
    let ε' :=  (ε) * 2 ^ (-m : ℤ)
    refine (MeasOpenCoverTendstoMeasUniv (S := S) (U := fun i ↦ ball (D i) (1 / (m+1)))
    (ε := ε') (hε := ?_) (fun i ↦ isOpen_ball) hcomp) ?_ (hcov m)
    · simp [ε']; exact ⟨εpos,(ENNReal.zpow_pos (Ne.symm (NeZero.ne' 2)) (ofNat_ne_top) (-↑m))⟩
    · simp [ε']; exact Left.mul_le_one (le_of_not_gt hεbound)
        (mod_cast (NNReal_pow_le_one (-m) 2 (by simp) (by simp)))
  choose! km hbound using id byclaim
  -- This is a set we can construct to show tightness
  let bigK := ⋂ m, ⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1)))
  have bigcalc (μ : ProbabilityMeasure X) (hs : μ ∈ S) := calc
    μ.toMeasure (bigK)ᶜ
    _ = μ.toMeasure (⋃ m,(⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      simp only [bigK, compl_iInter, compl_iUnion]
    _ ≤ ∑' m, μ.toMeasure ((⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      apply measure_iUnion_le
    _ = ∑' m, (1 - μ.toMeasure (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) := by
      congr! with m
      rw [measure_compl ?_ (by simp)]
      · simp
      · refine Finite.measurableSet_biUnion ?_ (fun b a ↦ measurableSet_closure)
        · simp only [Nat.le_eq]
          refine BddAbove.finite <| bddAbove_def.mpr ?_
          use (km (m + 1) + 1)
          exact fun y a ↦ Nat.le_add_right_of_le a
    _ ≤ (∑' (m : ℕ), (ε : ENNReal) * 2 ^ (-(m+1) : ℤ)) := by
      apply lt_geom_series S D ε μ hs km hbound
    _ = ε := by exact mul_shifted_geom_series ε
  -- Final proof
  use bigK
  constructor
  -- Compactness first
  · refine isCompact_of_totallyBounded_isClosed ?_ ?_
    --Totally bounded
    · refine Metric.totallyBounded_iff.mpr ?_
      intro δ δpos
      -- t should be image under D of the set of numbers less than km of 1/δ.ceil
      refine ⟨D '' .Iic (km (⌊δ⁻¹⌋₊ + 1)), (Set.finite_Iic _).image _, ?_⟩
      simp only [one_div, mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, bigK]
      calc
            ⋂ m, ⋃ i ≤ km (m + 1), closure (ball (D i) (m + 1)⁻¹)
        _ ⊆ ⋃ i ≤ km (⌊δ⁻¹⌋₊ + 1), closure (ball (D i) (⌊δ⁻¹⌋₊ + 1)⁻¹) := iInter_subset ..
        _ ⊆ ⋃ i ≤ km (⌊δ⁻¹⌋₊ + 1), ball (D i) δ := by
            gcongr
            exact closure_ball_subset_closedBall.trans <| closedBall_subset_ball <|
              inv_lt_of_inv_lt₀ δpos <| Nat.lt_floor_add_one _
    -- Closedness
    · simp only [one_div, bigK]
      refine isClosed_iInter ?_; intro n
      refine Finite.isClosed_biUnion ?_ (fun _ _ ↦ isClosed_closure)
      · refine Finite.ofFinset (Finset.Iic (km (n+1))) fun x ↦ ?_
        simp only [Finset.mem_Iic, Nat.le_eq]; exact Eq.to_iff rfl
  simp only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact bigcalc

end

end MeasureTheory
