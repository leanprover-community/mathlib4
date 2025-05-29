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
  by_cases hd : DiscreteTopology K
  · have : DiscreteTopology 𝒪[K] := inferInstance
    infer_instance
  rw [isLinearTopology_iff_hasBasis_ideal]
  have := (hasBasis_nhds_zero K Γ₀).comap (Subtype.val : 𝒪[K] → K)
  have hn0 : 𝓝 (0 : 𝒪[K]) = comap Subtype.val (𝓝 0) := nhds_induced Subtype.val 0
  rw [← hn0] at this
  refine this.to_hasBasis ?_ ?_
  · intro r _
    refine ⟨idealBall _ r, (isOpen_idealBall _ r).mem_nhds <| zero_mem _, ?_⟩
    simp
  · intro I hI
    have hI' : I ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.bot_coe] at hI
      have : DiscreteTopology 𝒪[K] := by
        rw [discreteTopology_iff_singleton_mem_nhds]
        intro y
        simpa using singleton_add_mem_nhds_of_nhds_zero y hI
      rw [Valued.discreteTopology_valuationRing_iff_discreteTopology] at this
      contradiction
    obtain ⟨x, hx, hx0⟩ : ∃ y ∈ I, y ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI'
    replace hx0 : Valued.v (x : K) ≠ 0 := by simp [hx0]
    refine ⟨Units.mk0 _ hx0, trivial, ?_⟩
    rw [Set.preimage_subset_iff]
    exact idealBall_v_le_of_mem hx hx0
