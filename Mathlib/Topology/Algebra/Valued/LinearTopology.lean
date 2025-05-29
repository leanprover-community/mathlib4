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
    IsLinearTopology 𝒪[K] 𝒪[K] := by
  -- a linear topology in this case means a basis of submodules, which our valued field has
  -- thanks to `Valued.hasBasis_nhds_zero`; however, we need to transfer that basis of submodules
  -- to a basis of ideals in the valuation ring, via `Subtype.val : 𝒪[K] → K`
  -- later, we will need to deal with the case of the trivial ideal,
  -- which is open iff the topology is discrete, so we will claim that the topology is not discrete
  -- because the discrete topology case is trivially `IsLinearTopology`
  by_cases hd : DiscreteTopology K
  · have : DiscreteTopology 𝒪[K] := inferInstance
    infer_instance
  rw [isLinearTopology_iff_hasBasis_ideal]
  -- we will need to provide a basis of open ideals that are neighborhoods of zero
  -- which we almost have, thanks to `Valued.hasBasis_nhds_zero`
  have := (hasBasis_nhds_zero K Γ₀).comap (Subtype.val : 𝒪[K] → K)
  -- we need to convert the comap-ed neighborhood of zero of the field to the neighborhood of zero
  -- of the valuation ring,
  have hn0 : 𝓝 (0 : 𝒪[K]) = comap Subtype.val (𝓝 0) := nhds_induced Subtype.val 0
  rw [← hn0] at this
  refine this.to_hasBasis ?_ ?_
  · -- easy implication: given a `r : Γ₀ˣ`, we have an open ideal that is a neighborhood of zero
    -- and is inside the open ball
    intro r _
    refine ⟨idealBall _ r, (isOpen_idealBall _ r).mem_nhds <| zero_mem _, ?_⟩
    simp
  · -- harder implication: given an open ideal `I` that is a neighborhood of zero,
    -- find an open ball in it. We need to get some `r : Γ₀ˣ` (really, `r ≠ 0`).
    -- We will construct such an `r` from a nontrivial element of `I`,
    -- since `I` must not be trivial itself.
    -- If it was trivial, then it could not have been open, since then a singleton would be open,
    -- which contradicts the assumption that the topology is not discrete.
    intro I hI
    have hI' : I ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.bot_coe] at hI
      have : DiscreteTopology 𝒪[K] := by
        rw [discreteTopology_iff_singleton_mem_nhds]
        intro y
        simpa using singleton_add_mem_nhds_of_nhds_zero y hI
      rw [Valued.discreteTopology_valuationRing_iff_discreteTopology] at this
      contradiction
    -- We now extract a nontrivial `x`, which will have a nonzero valuation `r := v x`,
    -- which we lift into the units `Γ₀ˣ`. The ideal ball associated to that `r` is necessarily
    -- contained in `I`.
    obtain ⟨x, hx, hx0⟩ : ∃ y ∈ I, y ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI'
    replace hx0 : Valued.v (x : K) ≠ 0 := by simp [hx0]
    refine ⟨Units.mk0 _ hx0, trivial, ?_⟩
    rw [Set.preimage_subset_iff]
    exact idealBall_v_le_of_mem hx hx0
