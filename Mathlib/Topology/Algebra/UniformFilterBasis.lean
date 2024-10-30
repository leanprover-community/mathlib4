/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.FilterBasis

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open uniformity Filter

open Filter

open scoped Uniformity

namespace Filter.IsAddGroupBasis

variable {G : Type*} {ι : Type*} {p : ι → Prop} {s : ι → Set G} [AddCommGroup G]
  (h : IsAddGroupBasis p s)

-- TODO(Anatole): Prove `UniformAddGroup` from `Filter.IsAddGroupBasis` like we do for topologies

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ h.topology h.topologicalAddGroup

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected instance (priority := 100) uniformAddGroup : @UniformAddGroup G h.uniformSpace _ :=
  @comm_topologicalAddGroup_is_uniform G _ h.topology h.topologicalAddGroup

theorem cauchy_iff {F : Filter G} :
    @Cauchy G h.uniformSpace F ↔
      F.NeBot ∧ ∀ i, p i → ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ s i := by
  letI := h.uniformSpace
  haveI := h.uniformAddGroup
  suffices F ×ˢ F ≤ uniformity G ↔ ∀ i, p i → ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ s i by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff h.nhds_zero_hasBasis, @forall_swap (_ ∈ _) G]

end Filter.IsAddGroupBasis
