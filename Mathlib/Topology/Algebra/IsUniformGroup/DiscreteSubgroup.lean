/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.GroupTheory.Commensurable
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Discrete subgroups of topological groups
-/

open Filter Topology Uniformity

variable {G : Type*} [Group G] [TopologicalSpace G]


/-- If `G` has a topology, and `H ≤ K` are subgroups, then `H` as a subgroup of `K` is homeomorphic
to `H` as a subgroup of `G`. This is `subgroupOfEquivOfLe` bundled as a `Homeomorph`. -/
@[to_additive]
def Subgroup.subgroupOfHomeomorphOfLe {G : Type*} [Group G] [TopologicalSpace G]
    {H K : Subgroup G} (h : H ≤ K) :
    (H.subgroupOf K) ≃ₜ H :=
  (subgroupOfEquivOfLe h).toHomeomorph (by
    simp only [subgroupOfEquivOfLe, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, Topology.IsInducing.subtypeVal.isOpen_iff, SetLike.coe_sort_coe,
      exists_exists_and_eq_and]
    simpa only [Set.ext_iff, Subtype.forall, mem_subgroupOf] using fun s ↦ exists_congr
      fun t ↦ and_congr_right fun _ ↦ ⟨fun aux g hgh ↦ aux g (h hgh) hgh, by grind⟩)

variable [IsTopologicalGroup G]

attribute [local instance] IsTopologicalGroup.toUniformSpace

@[to_additive]
instance Subgroup.isClosed_of_discrete [T2Space G] {H : Subgroup G} [DiscreteTopology H] :
    IsClosed (H : Set G) := by
  obtain ⟨V, V_in, VH⟩ : ∃ (V : Set G), V ∈ 𝓝 (1 : G) ∧ V ∩ (H : Set G) = {1} :=
    nhds_inter_eq_singleton_of_mem_discrete H.one_mem
  have : (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ 𝓤 G := preimage_mem_comap V_in
  apply isClosed_of_spaced_out this
  intro h h_in h' h'_in
  contrapose!
  simp only [Set.mem_preimage, not_not]
  rintro (hyp : h' / h ∈ V)
  have : h' / h ∈ ({1} : Set G) := VH ▸ Set.mem_inter hyp (H.div_mem h'_in h_in)
  exact (eq_of_div_eq_one this).symm

@[to_additive]
lemma Subgroup.tendsto_coe_cofinite_of_discrete [T2Space G] (H : Subgroup G) [DiscreteTopology H] :
    Tendsto ((↑) : H → G) cofinite (cocompact _) :=
  IsClosed.tendsto_coe_cofinite_of_discreteTopology inferInstance inferInstance

@[to_additive]
lemma MonoidHom.tendsto_coe_cofinite_of_discrete [T2Space G] {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) (hf' : DiscreteTopology f.range) :
    Tendsto f cofinite (cocompact _) := by
  replace hf : Function.Injective f.rangeRestrict := by simpa
  exact f.range.tendsto_coe_cofinite_of_discrete.comp hf.tendsto_cofinite

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

@[to_additive]
lemma Subgroup.Commensurable.discreteTopology_iff
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H K : Subgroup G} (h : Commensurable H K) :
    DiscreteTopology H ↔ DiscreteTopology K := by
  rw [Commensurable, ← Subgroup.inf_relIndex_left H K, ← Subgroup.inf_relIndex_right H K] at h
  rw [← Subgroup.discreteTopology_iff_of_finite_relIndex inf_le_right h.1,
    ← Subgroup.discreteTopology_iff_of_finite_relIndex inf_le_left h.2]
