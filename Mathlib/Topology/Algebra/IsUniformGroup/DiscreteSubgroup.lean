/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.GroupTheory.Commensurable
import Mathlib.Topology.Algebra.ContinuousMonoidHom
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
lemma Subgroup.discreteTopology_iff_of_index_ne_zero {H : Subgroup G} (hind : H.index ≠ 0) :
    DiscreteTopology H ↔ DiscreteTopology G := by
  refine ⟨fun hH ↦ ?_, fun hG ↦ instDiscreteTopologySubtype⟩
  let s (i : G ⧸ H) : Set G := QuotientGroup.mk ⁻¹' {i}
  have : ⋃ i, s i = Set.univ := by
    simpa only [Set.eq_univ_iff_forall, Set.mem_iUnion] using fun i ↦ ⟨⟦i⟧, rfl⟩
  rw [← (Homeomorph.Set.univ G).discreteTopology_iff]
  suffices h : DiscreteTopology (⋃ i, s i) by convert h <;> rw [this]
  haveI : Fintype (G ⧸ H) := fintypeOfIndexNeZero hind
  apply discreteTopology_iUnion_fintype
  · -- show `s i` is discrete for all `i`
    rintro ⟨k⟩
    change DiscreteTopology (QuotientGroup.mk ⁻¹' {⟦k⟧})
    rw [(Set.image_singleton ▸ QuotientGroup.preimage_image_mk_eq_mul H {k} :)]
    exact ((Homeomorph.mulLeft k).subtype (p := (· ∈ H)) (by simp)).discreteTopology
  · -- show `s i` is closed for all `i`
    rintro ⟨k⟩
    change IsClosed (QuotientGroup.mk ⁻¹' {⟦k⟧})
    rw [(Set.image_singleton ▸ QuotientGroup.preimage_image_mk_eq_mul H {k} :)]
    convert (Homeomorph.mulLeft k).isClosed_image.mpr H.isClosed_of_discrete
    ext g
    simp only [Set.singleton_mul, Set.image_mul_left, Set.mem_preimage, Homeomorph.coe_mulLeft]

@[to_additive]
lemma Subgroup.discreteTopology_iff_of_finite_relIndex {H K : Subgroup G} (hHK : H ≤ K)
    (hind : H.relIndex K ≠ 0) : DiscreteTopology H ↔ DiscreteTopology K := by
  rw [← discreteTopology_iff_of_index_ne_zero hind,
    (subgroupOfContinuousMulEquivOfLe hHK).symm.discreteTopology_iff]

@[to_additive]
lemma Subgroup.Commensurable.discreteTopology_iff
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H K : Subgroup G} (h : Commensurable H K) :
    DiscreteTopology H ↔ DiscreteTopology K := by
  rw [Commensurable, ← Subgroup.inf_relIndex_left H K, ← Subgroup.inf_relIndex_right H K] at h
  rw [← Subgroup.discreteTopology_iff_of_finite_relIndex inf_le_right h.1,
    ← Subgroup.discreteTopology_iff_of_finite_relIndex inf_le_left h.2]
