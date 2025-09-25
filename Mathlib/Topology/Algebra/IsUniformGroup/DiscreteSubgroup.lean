/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Discrete subgroups of topological groups

Note that the instance `Subgroup.isClosed_of_discrete` does not live here, in order that it can
be used in other files without requiring lots of group-theoretic imports.
-/

open Filter Topology Uniformity

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- If `G` has a topology, and `H ≤ K` are subgroups, then `H` as a subgroup of `K` is homeomorphic
to `H` as a subgroup of `G`. This is `subgroupOfEquivOfLe` bundled as a `Homeomorph`. -/
@[to_additive (attr := simps! apply symm_apply) /-- If `G` has a topology, and `H ≤ K` are
subgroups, then `H` as a subgroup of `K` is homeomorphic to `H` as a subgroup of `G`. This is
`subgroupOfEquivOfLe` bundled as a `Homeomorph`.-/]
def Subgroup.subgroupOfHomeomorphOfLe {G : Type*} [Group G] [TopologicalSpace G]
    {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K) ≃ₜ H :=
  (subgroupOfEquivOfLe hHK).toHomeomorph (by
    simp only [subgroupOfEquivOfLe, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, Topology.IsInducing.subtypeVal.isOpen_iff, SetLike.coe_sort_coe,
      exists_exists_and_eq_and]
    simpa only [Set.ext_iff, Subtype.forall, mem_subgroupOf] using fun s ↦ exists_congr
      fun t ↦ and_congr_right fun _ ↦ ⟨fun aux g hgh ↦ aux g (hHK hgh) hgh, by grind⟩)

@[to_additive]
lemma Subgroup.subgroupOfHomeomorphOfLe_toEquiv {G : Type*} [Group G] [TopologicalSpace G]
    {H K : Subgroup G} (hHK : H ≤ K) :
    (subgroupOfHomeomorphOfLe hHK : H.subgroupOf K ≃ H) = subgroupOfEquivOfLe hHK := by
  rfl

variable [IsTopologicalGroup G]

/-- If `G` is a topological group and `H` a finite-index subgroup, then `G` is topologically
discrete iff `H` is. -/
@[to_additive]
lemma Subgroup.discreteTopology_iff_of_index_ne_zero
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H : Subgroup G} (hind : H.index ≠ 0) :
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
lemma Subgroup.discreteTopology_iff_of_finite_relIndex
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H K : Subgroup G} (hHK : H ≤ K) (hind : H.relIndex K ≠ 0) :
    DiscreteTopology H ↔ DiscreteTopology K := by
  rw [← discreteTopology_iff_of_index_ne_zero hind,
    (subgroupOfHomeomorphOfLe hHK).symm.discreteTopology_iff]
