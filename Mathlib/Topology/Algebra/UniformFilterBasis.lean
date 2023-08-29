/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.UniformGroup

#align_import topology.algebra.uniform_filter_basis from "leanprover-community/mathlib"@"531db2ef0fdddf8b3c8dcdcd87138fe969e1a81a"

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
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
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.isTopologicalAddGroup
#align add_group_filter_basis.uniform_space AddGroupFilterBasis.uniformSpace

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem uniformAddGroup : @UniformAddGroup G B.uniformSpace _ :=
  @comm_topologicalAddGroup_is_uniform G _ B.topology B.isTopologicalAddGroup
#align add_group_filter_basis.uniform_add_group AddGroupFilterBasis.uniformAddGroup

theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.uniformSpace F ↔
      F.NeBot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U := by
  letI := B.uniformSpace
  -- ⊢ Cauchy F ↔ NeBot F ∧ ∀ (U : Set G), U ∈ B → ∃ M, M ∈ F ∧ ∀ (x : G), x ∈ M →  …
  haveI := B.uniformAddGroup
  -- ⊢ Cauchy F ↔ NeBot F ∧ ∀ (U : Set G), U ∈ B → ∃ M, M ∈ F ∧ ∀ (x : G), x ∈ M →  …
  suffices F ×ˢ F ≤ uniformity G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine' ⟨h', _⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  -- ⊢ map (fun x => x.snd - x.fst) (F ×ˢ F) ≤ nhds 0 ↔ ∀ (U : Set G), U ∈ B → ∃ M, …
  change Tendsto _ _ _ ↔ _
  -- ⊢ Tendsto (fun x => x.snd - x.fst) (F ×ˢ F) (nhds 0) ↔ ∀ (U : Set G), U ∈ B →  …
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_swap (_ ∈ _) G]
  -- 🎉 no goals
#align add_group_filter_basis.cauchy_iff AddGroupFilterBasis.cauchy_iff

end AddGroupFilterBasis
