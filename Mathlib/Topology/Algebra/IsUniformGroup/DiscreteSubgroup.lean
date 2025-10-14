/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.GroupTheory.Commensurable
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Discrete subgroups of topological groups

Note that the instance `Subgroup.isClosed_of_discrete` does not live here, in order that it can
be used in other files without requiring lots of group-theoretic imports.
-/

open Filter Topology Uniformity

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- If `G` has a topology, and `H ≤ K` are subgroups, then `H` as a subgroup of `K` is isomorphic,
as a topological group, to `H` as a subgroup of `G`. This is `subgroupOfEquivOfLe` upgraded to a
`ContinuousMulEquiv`. -/
@[to_additive (attr := simps! apply) /-- If `G` has a topology, and `H ≤ K` are
subgroups, then `H` as a subgroup of `K` is isomorphic, as a topological group, to `H` as a subgroup
of `G`. This is `addSubgroupOfEquivOfLe` upgraded to a `ContinuousAddEquiv`.-/]
def Subgroup.subgroupOfContinuousMulEquivOfLe {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K) ≃ₜ* H :=
  (subgroupOfEquivOfLe hHK).toContinuousMulEquiv (by
    simp only [subgroupOfEquivOfLe, Topology.IsInducing.subtypeVal.isOpen_iff,
      exists_exists_and_eq_and]
    simpa [Set.ext_iff] using fun s ↦ exists_congr
      fun t ↦ and_congr_right fun _ ↦ ⟨fun aux g hgh ↦ aux g (hHK hgh) hgh, by grind⟩)

@[to_additive (attr := simp)]
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply
    {H K : Subgroup G} (hHK : H ≤ K) (g : H) :
    (subgroupOfContinuousMulEquivOfLe hHK).symm g = ⟨⟨g.1, hHK g.2⟩, g.2⟩ :=
  rfl

@[to_additive (attr := simp)]
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv {H K : Subgroup G} (hHK : H ≤ K) :
    (subgroupOfContinuousMulEquivOfLe hHK : H.subgroupOf K ≃* H) = subgroupOfEquivOfLe hHK := by
  rfl

variable [IsTopologicalGroup G] [T2Space G]

/-- If `G` is a topological group and `H` a finite-index subgroup, then `G` is topologically
discrete iff `H` is. -/
@[to_additive]
lemma Subgroup.discreteTopology_iff_of_finiteIndex {H : Subgroup G} [H.FiniteIndex] :
    DiscreteTopology H ↔ DiscreteTopology G := by
  refine ⟨fun hH ↦ ?_, fun hG ↦ inferInstance⟩
  suffices IsOpen (H : Set G) by
    rw [discreteTopology_iff_isOpen_singleton_one, isOpen_singleton_iff_nhds_eq_pure,
        ← H.coe_one, ← this.isOpenEmbedding_subtypeVal.map_nhds_eq, nhds_discrete, map_pure]
  exact H.isOpen_of_isClosed_of_finiteIndex Subgroup.isClosed_of_discrete

@[to_additive]
lemma Subgroup.discreteTopology_iff_of_isFiniteRelIndex {H K : Subgroup G} (hHK : H ≤ K)
    [IsFiniteRelIndex H K] : DiscreteTopology H ↔ DiscreteTopology K := by
  haveI : (H.subgroupOf K).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [← (subgroupOfContinuousMulEquivOfLe hHK).discreteTopology_iff,
    discreteTopology_iff_of_finiteIndex]

@[to_additive]
lemma Subgroup.Commensurable.discreteTopology_iff
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H K : Subgroup G} (h : Commensurable H K) :
    DiscreteTopology H ↔ DiscreteTopology K :=
  calc DiscreteTopology H ↔ DiscreteTopology ↑(H ⊓ K) :=
    haveI : IsFiniteRelIndex (H ⊓ K) H := ⟨Subgroup.inf_relIndex_left H K ▸ h.2⟩
    (Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ DiscreteTopology K :=
    haveI : IsFiniteRelIndex (H ⊓ K) K := ⟨Subgroup.inf_relIndex_right H K ▸ h.1⟩
    Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_right
