/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Valuation rings of valued fields have a linear topology

## Main Results
* `IsLinearTopology.isFractionRing`: for a ring `R` and its fraction field `K`, such that
  `algebraMap R K` is an open embedding, if `IsLinearTopology R R` then `IsLinearTopology R K`
* `IsLinearTopology.of_valued`: for a valued field `K`,
  the valuation ring `𝒪[K]` has a linear topology

-/

open Valued Filter Topology

-- TODO: find a better home for this
lemma IsLinearTopology.isFractionRing {R K : Type*} [CommRing R] [rTop : TopologicalSpace R]
    [ContinuousAdd R] [hl : IsLinearTopology R R]
    [CommRing K] [kTop : TopologicalSpace K] [ContinuousAdd K] -- inferrable from ContinuousAdd R?
    [Algebra R K] [IsFractionRing R K]  (h : IsOpenEmbedding (algebraMap R K)) :
    IsLinearTopology R K := by
  have ht : rTop = kTop.induced (algebraMap R K) := h.isInducing.eq_induced
  rw [isLinearTopology_iff_hasBasis_open_submodule] at hl ⊢
  rw [show (0 : K) = algebraMap R K 0 by simp, ← map_nhds_induced_of_mem]
  · have : rTop = kTop.induced (algebraMap R K) := h.isInducing.eq_induced
    subst this
    let _ : TopologicalSpace R := kTop.induced (algebraMap R K)
    refine (hl.map (algebraMap R K)).to_hasBasis ?_ ?_
    · intro I hI
      exact ⟨I.map (Algebra.linearMap _ _), h.isOpen_iff_image_isOpen.mp hI, subset_refl _⟩
    · intro I hI
      refine ⟨I.comap (Algebra.linearMap _ _), h.continuous.isOpen_preimage _ hI, ?_⟩
      simpa using subset_refl _
  · rw [← Set.image_univ, h.image_mem_nhds]
    simp

variable {R K Γ₀ : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

instance IsLinearTopology.of_valued' :
    IsLinearTopology 𝒪[K] 𝒪[K] := by
  -- TODO: link IsLinearTopology to ModuleFilterBasis
  rw [isLinearTopology_iff_hasBasis_open_submodule]
  have : (𝓝 (0 : K)).comap (Subtype.val : 𝒪[K] → K) = 𝓝 0 := by
    rw [show (0 : K) = ↑(0 : 𝒪[K]) by rfl, ← nhds_induced]
  rw [← this]
  refine ((hasBasis_nhds_zero K Γ₀).comap (Subtype.val : 𝒪[K] → K)).to_hasBasis ?_ ?_
  · exact fun r _ ↦ ⟨v.ltIdeal r, isOpen_ltIdeal _ _, subset_refl _⟩
  · intro I hI
    simp only [true_and]
    have : ((Subtype.val : 𝒪[K] → K) '' (I : Set 𝒪[K])) ∈ 𝓝 (0 : K) := by
      rw [show (0 : K) = ↑(0 : 𝒪[K]) by rfl]
      convert (isOpenEmbedding_algebraMap_integer K).image_mem_nhds.mpr _
      rw [mem_nhds_iff]
      exact ⟨_, subset_refl _, hI, zero_mem _⟩
    refine (mem_nhds_zero.mp this).imp ?_
    simp only [Set.preimage_setOf_eq]
    intro y hy
    exact (Set.preimage_subset hy Subtype.val_injective.injOn)

instance IsLinearTopology.of_valued :
    IsLinearTopology 𝒪[K] K :=
  .isFractionRing (isOpenEmbedding_algebraMap_integer _)
