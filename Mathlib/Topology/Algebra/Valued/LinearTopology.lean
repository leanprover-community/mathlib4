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
* `IsLinearTopology.of_valued`: for a valued field `K`,
  the valuation ring `𝒪[K]` has a linear topology

-/
open Valued Filter Topology

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

instance IsLinearTopology.of_valued :
    IsLinearTopology 𝒪[K] K := by
  rw [isLinearTopology_iff_hasBasis_open_submodule]
  apply (hasBasis_nhds_zero K Γ₀).to_hasBasis
  · exact fun r _ ↦ ⟨ltSubmodule K r, isOpen_ltSubmodule _ _, subset_rfl⟩
  · intro I hI
    simpa [mem_nhds_zero] using hI.mem_nhds I.zero_mem

instance IsLinearTopology.of_valued' :
    IsLinearTopology 𝒪[K] 𝒪[K] := by
  have : IsLinearTopology 𝒪[K] K := inferInstance
  rw [isLinearTopology_iff_hasBasis_open_submodule] at this
  have := this.comap (Subtype.val : 𝒪[K] → K)
  -- we need to convert the comap-ed neighborhood of zero of the field to the neighborhood of zero
  -- of the valuation ring,
  have hn0 : 𝓝 (0 : 𝒪[K]) = comap Subtype.val (𝓝 0) := nhds_induced Subtype.val 0
  rw [← hn0] at this
  rw [isLinearTopology_iff_hasBasis_open_submodule]
  refine this.to_hasBasis ?_ ?_
  · intro I hI
    exact ⟨I.comap (Algebra.linearMap 𝒪[K] K), continuous_subtype_val.isOpen_preimage _ hI,
      subset_refl _⟩
  · intro I hI
    refine ⟨Submodule.map (Algebra.linearMap 𝒪[K] K) I, ?_,
      (Set.preimage_image_eq _ (Subtype.val_injective)).le⟩
    simp only [Submodule.map_coe, Algebra.linearMap_apply]
    rwa [← (isOpenEmbedding_algebraMap_integer _).isOpen_iff_image_isOpen]
