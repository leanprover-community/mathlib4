/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Tight sets of measures and tight measures

A set of measures is tight if for all `0 < ε`, there exists a compact set `K` such that for all
measures in the set, the complement of `K` has measure at most `ε`. A single measure `μ` is said
to be tight if the singleton `{μ}` is tight.

## Main definitions

* `MeasureTheory.IsTightMeasureSet`: A set of measures `S` is tight if for all `0 < ε`, there exists
  a compact set `K` such that for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `⨆ μ ∈ S, μ` tends to `0` along the
  filter of cocompact sets.
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` establishes equivalence between
  the two definitions.
* `MeasureTheory.IsTight`: A measure `μ` is tight if for all `0 < ε`, there exists `K`
  compact such that `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `μ` tends to `0` along the
  filter of cocompact sets.
  `isTight_iff_exists_isCompact_measure_compl_le` establishes equivalence of the two definitions.

## Main statements

* An instance showing that every finite, inner-regular measure on a T2 space is tight.

-/

open Filter Set

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {μ ν : Measure α}
  {S T : Set (Measure α)}

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the definition above
in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
def IsTightMeasureSet (S : Set (Measure α)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact α).smallSets (𝓝 0)

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`.
This is formulated in terms of filters, and proven equivalent to the usual definition
in `isTight_iff_exists_isCompact_measure_compl_le`. -/
class IsTight (μ : Measure α) : Prop where
  tendsto_cocompact : Tendsto μ (cocompact α).smallSets (𝓝 0)

lemma Measure.tendsto_cocompact (μ : Measure α) [IsTight μ] :
    Tendsto μ (cocompact α).smallSets (𝓝 0) := IsTight.tendsto_cocompact

section IsTightMeasureSet

@[simp]
lemma IsTightMeasureSet_singleton_iff : IsTightMeasureSet {μ} ↔ IsTight μ := by
  simp only [IsTightMeasureSet, mem_singleton_iff, iSup_iSup_eq_left]
  exact ⟨fun h ↦ ⟨h⟩, fun _ ↦ μ.tendsto_cocompact⟩

lemma IsTightMeasureSet_singleton (μ : Measure α) [IsTight μ] : IsTightMeasureSet {μ} := by
  rw [IsTightMeasureSet_singleton_iff]
  infer_instance

/-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
for all `μ ∈ S`, `μ Kᶜ ≤ ε`. -/
lemma IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
    exact ⟨K, h1, hA Kᶜ h2⟩
  · obtain ⟨K, h1, h2⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS ↦ (μ.mono hA).trans (h2 μ hμS)⟩

/-- In a compact space, every set of measures is tight. -/
lemma IsTightMeasureSet.of_compactSpace [CompactSpace α] : IsTightMeasureSet S := by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ ↦ mem_of_mem_nhds

lemma IsTightMeasureSet.subset (hT : IsTightMeasureSet T) (hST : S ⊆ T) :
    IsTightMeasureSet S :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ ↦ by simp)
    (iSup_le_iSup_of_subset hST)

end IsTightMeasureSet

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`. -/
lemma isTight_iff_exists_isCompact_measure_compl_le :
    IsTight μ ↔ ∀ ε, 0 < ε → ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε := by
  simp [← IsTightMeasureSet_singleton_iff, IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]

lemma Measure.exists_isCompact_measure_compl_le (μ : Measure α) [h : IsTight μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε :=
  isTight_iff_exists_isCompact_measure_compl_le.mp h ε hε

namespace IsTight

lemma of_exists_isCompact_measure_compl_le (h : ∀ ε, 0 < ε → ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ ε) :
    IsTight μ := isTight_iff_exists_isCompact_measure_compl_le.mpr h

lemma exists_isSigmaCompact_measure_eq [IsTight μ] :
    ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ := by
  choose! K hK
    using (fun (n : ℕ) ↦ μ.exists_isCompact_measure_compl_le (by simp : 0 < 1/(n : ℝ≥0∞)))
  use ⋃ n, K n, isSigmaCompact_iUnion_of_isCompact _ fun _ ↦ (hK _).1
  rw [measure_congr]
  rw [ae_eq_univ, Set.compl_iUnion, ← le_zero_iff]
  refine le_of_forall_lt' fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  exact lt_of_le_of_lt ((measure_mono <| Set.iInter_subset _ n).trans <|
    (inv_eq_one_div (n : ENNReal)).symm ▸ (hK n).2) hn

/-- In a compact space, every measure is tight. -/
instance [CompactSpace α] : IsTight μ := by
  rw [← IsTightMeasureSet_singleton_iff]
  exact .of_compactSpace

lemma mono [IsTight ν] (h : μ ≤ ν) : IsTight μ where
  tendsto_cocompact := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ν.tendsto_cocompact (fun _ ↦ by simp) h

instance [IsTight μ] {s : Set α} : IsTight (μ.restrict s) := mono μ.restrict_le_self

instance [IsTight μ] [IsTight ν] : IsTight (μ + ν) where
  tendsto_cocompact := by
    simpa only [add_zero] using Filter.Tendsto.add μ.tendsto_cocompact ν.tendsto_cocompact

instance (c : ℝ≥0) [hμ : IsTight μ] : IsTight (c • μ) := by
  rw [isTight_iff_exists_isCompact_measure_compl_le] at hμ ⊢
  intro ε hε
  have hεc : 0 < ε / c := by simp [hε.ne']
  obtain ⟨K, hK, hKc⟩ := hμ (ε / c) hεc
  exact ⟨K, hK, ENNReal.mul_le_of_le_div' hKc⟩

/-- Tight measures on T2 spaces that assign finite measure to compact sets are finite. -/
instance [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [hk : IsFiniteMeasureOnCompacts μ] [IsTight μ] :
    IsFiniteMeasure μ where
  measure_univ_lt_top := by
    obtain ⟨K, hK, hμ⟩ := μ.exists_isCompact_measure_compl_le zero_lt_one
    rw [← measure_add_measure_compl hK.measurableSet, ENNReal.add_lt_top]
    exact ⟨hk.lt_top_of_isCompact hK, hμ.trans_lt ENNReal.one_lt_top⟩

/-- Inner regular finite measures on T2 spaces are tight. -/
instance [T2Space α] [OpensMeasurableSpace α] [IsFiniteMeasure μ] [μ.InnerRegular] :
    IsTight μ := by
  refine of_exists_isCompact_measure_compl_le fun ε hε ↦ ?_
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) (zero_le'.trans_lt hεr).ne'
      hε.ne'
    obtain ⟨K, _, hK_compact, hKμ⟩ := MeasurableSet.univ.exists_lt_isCompact hεr'
    refine ⟨K, hK_compact, ?_⟩
    rw [measure_compl hK_compact.measurableSet (measure_ne_top μ _), tsub_le_iff_right]
    rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
    exact hKμ.le
  | inr hεr => exact ⟨∅, isCompact_empty, by rwa [Set.compl_empty]⟩

end IsTight

end MeasureTheory
