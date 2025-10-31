/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Uniform properties of neighborhood bases in topological algebra

This file contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type*} [AddCommGroup G] (B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniformSpace : UniformSpace G :=
  @IsTopologicalAddGroup.toUniformSpace G _ B.topology B.isTopologicalAddGroup

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem isUniformAddGroup : @IsUniformAddGroup G B.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup G _ B.topology B.isTopologicalAddGroup

theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.uniformSpace F ↔
      F.NeBot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U := by
  letI := B.uniformSpace
  haveI := B.isUniformAddGroup
  suffices F ×ˢ F ≤ uniformity G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_swap (_ ∈ _) G]

end AddGroupFilterBasis
