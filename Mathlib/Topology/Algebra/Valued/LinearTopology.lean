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
  -- a linear topology in this case means a basis of submodules, which our valued field has
  -- thanks to `Valued.hasBasis_nhds_zero`
  -- later, we will need to deal with the case of the trivial submodule,
  -- which is open iff the topology is discrete, so we will claim that the topology is not discrete
  -- because the discrete topology case is trivially `IsLinearTopology`
  by_cases hd : DiscreteTopology K
  · infer_instance
  rw [isLinearTopology_iff_hasBasis_open_submodule]
  simp_rw [hasBasis_iff, mem_nhds_zero]
  intro t
  constructor
  · rintro ⟨r, hr⟩
    -- easy implication: given a `r : Γ₀ˣ`, we have an open submodule that is an open ball
    have : (algebraMap 𝒪[K] K : 𝒪[K] → K) = Subtype.val := rfl
    -- this is `algebraMap (Ideal K) (Submodule 𝒪[K] K)` but does not have lemmas about it
    refine ⟨Submodule.map (Algebra.linearMap 𝒪[K] K) (idealBall K r), ?_, ?_⟩
    · simp only [Submodule.map_coe, Algebra.linearMap_apply, coe_idealBall]
      rw [← (isOpenEmbedding_algebraMap_integer _).isOpen_iff_image_isOpen]
      exact isOpen_idealBall K r
    · refine hr.trans' ?_
      intro
      simp +contextual [this]
  · rintro ⟨I, hI, hIt⟩
   -- harder implication: given an open submodule `I`, find an open ball in it.
   -- We need to get some `r : Γ₀ˣ` (really, `r ≠ 0`).
   -- We will construct such an `r` from a nontrivial element of `I`,
   -- since `I` must not be trivial itself.
   -- If it was trivial, then it could not have been open, since then a singleton would be open,
   -- which contradicts the assumption that the topology is not discrete.
    have hI' : I ≠ ⊥ := by
      rintro rfl
      have : DiscreteTopology K := by
        rw [discreteTopology_iff_singleton_mem_nhds]
        intro y
        simpa using singleton_add_mem_nhds_of_nhds_zero y (hI.mem_nhds rfl)
      contradiction
    -- We now extract a nontrivial `x`, which will have a nonzero valuation `r := v x`,
    -- which we lift into the units `Γ₀ˣ`. The submodule ball associated to that `r` is necessarily
    -- contained in `I`.
    obtain ⟨x, hx, hx0⟩ : ∃ y ∈ I, y ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI'
    replace hx0 : Valued.v (x : K) ≠ 0 := by simp [hx0]
    refine ⟨Units.mk0 _ hx0, hIt.trans' ?_⟩
    exact submoduleBall_v_le_of_mem hx hx0

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
