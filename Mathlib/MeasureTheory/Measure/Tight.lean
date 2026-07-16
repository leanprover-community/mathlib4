/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker, Arav Bhattacharyya
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular

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

open Filter Set TopologicalSpace

open scoped Topology

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} {S T : Set (Measure 𝓧)}

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
  convert! Tendsto.sup_nhds hS hT
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

/-- A set of measures on a product space is tight if both marginals are tight. -/
lemma prodMk {m𝓨 : MeasurableSpace 𝓨} [TopologicalSpace 𝓨] {μ : Set (Measure (𝓧 × 𝓨))}
    (hμ₁ : IsTightMeasureSet (Measure.fst '' μ)) (hμ₂ : IsTightMeasureSet (Measure.snd '' μ)) :
    IsTightMeasureSet μ := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ₁ hμ₂ ⊢
  intro ε hε
  obtain ⟨K₁, hK₁_compact, hK₁_le⟩ := hμ₁ (ε / 2) (by aesop)
  obtain ⟨K₂, hK₂_compact, hK₂_le⟩ := hμ₂ (ε / 2) (by aesop)
  refine ⟨K₁ ×ˢ K₂, hK₁_compact.prod hK₂_compact, fun κ hκ_mem ↦ ?_⟩
  grw [compl_prod_eq_union, measure_union_le, ← ENNReal.add_halves (a := ε)]
  apply add_le_add
  · specialize hK₁_le _ <| mem_image_of_mem _ hκ_mem
    grw [Measure.fst, ← Measure.le_map_apply (by fun_prop)] at hK₁_le
    simpa [prod_univ] using hK₁_le
  · specialize hK₂_le _ <| Set.mem_image_of_mem _ hκ_mem
    grw [Measure.snd, ← Measure.le_map_apply (by fun_prop)] at hK₂_le
    simpa [univ_prod] using hK₂_le

end IsTightMeasureSet
end Basic

end MeasureTheory
