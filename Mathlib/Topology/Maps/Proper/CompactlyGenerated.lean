/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Maps.Proper.Basic

/-!
# A map is proper iff preimage of compact sets are compact

This file proves that if `Y` is a Hausdorff and compactly generated space, a continuous map
`f : X → Y` is proper if and only if preimage of compact sets are compact.
-/

open Set Filter

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space Y] [CompactlyGeneratedSpace Y]
variable {f : X → Y}

/-- If `Y` is Hausdorff and compactly generated, then proper maps `X → Y` are exactly
continuous maps such that the preimage of any compact set is compact. This is in particular true
if `Y` is Hausdorff and sequential or locally compact. -/
theorem isProperMap_iff_isCompact_preimage :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) where
  mp hf := ⟨hf.continuous, fun _ ↦ hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ ↦ isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun _ hs ↦ CompactlyGeneratedSpace.isClosed
      fun _ hK ↦ image_inter_preimage .. ▸ (((h hK).inter_left hs).image hf).isClosed,
      fun _ ↦ h isCompact_singleton⟩

@[deprecated CompactlyGeneratedSpace.isClosed_iff_of_t2 (since := "2024-10-10")]
theorem compactlyGenerated_of_weaklyLocallyCompactSpace [T2Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} : IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K) := by
  refine ⟨fun hs K hK ↦ hs.inter hK.isClosed, fun h ↦ ?_⟩
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h hK) x ℱ hℱ₁
    (inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| le_principal_iff.2 K_mem)) hℱ₃

@[deprecated isProperMap_iff_isCompact_preimage (since := "2024-10-10")]
theorem WeaklyLocallyCompactSpace.isProperMap_iff_isCompact_preimage [T2Space Y]
    [WeaklyLocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) :=
  _root_.isProperMap_iff_isCompact_preimage

@[deprecated CompactlyGeneratedSpace.isClosed_iff_of_t2 (since := "2024-10-10")]
theorem compactlyGenerated_of_sequentialSpace [T2Space X] [SequentialSpace X] {s : Set X} :
    IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K) := by
  refine ⟨fun hs K hK ↦ hs.inter hK.isClosed,
    fun h ↦ SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦
    mem_of_mem_inter_left ((h hup.isCompact_insert_range).mem_of_tendsto hup ?_)⟩
  simp only [mem_inter_iff, mem_insert_iff, mem_range, exists_apply_eq_apply, or_true, and_true,
    eventually_atTop, ge_iff_le]
  exact ⟨0, fun n _ ↦ hu n⟩

@[deprecated isProperMap_iff_isCompact_preimage (since := "2024-10-10")]
theorem SequentialSpace.isProperMap_iff_isCompact_preimage [T2Space Y] [SequentialSpace Y] :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) :=
  _root_.isProperMap_iff_isCompact_preimage

/-- Version of `isProperMap_iff_isCompact_preimage` in terms of `cocompact`. -/
lemma isProperMap_iff_tendsto_cocompact :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont ↦
    ⟨fun H K hK ↦ (H hK).compl_mem_cocompact, fun H K hK ↦ ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact hK'.of_isClosed_subset (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)

@[deprecated isProperMap_iff_tendsto_cocompact (since := "2024-10-10")]
lemma WeaklyLocallyCompactSpace.isProperMap_iff_tendsto_cocompact [T2Space Y]
    [WeaklyLocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) :=
  _root_.isProperMap_iff_tendsto_cocompact

@[deprecated isProperMap_iff_tendsto_cocompact (since := "2024-10-10")]
lemma SequentialSpace.isProperMap_iff_tendsto_cocompact [T2Space Y] [SequentialSpace Y] :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) :=
  _root_.isProperMap_iff_tendsto_cocompact
