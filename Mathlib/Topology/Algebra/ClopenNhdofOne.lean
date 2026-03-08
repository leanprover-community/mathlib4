/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song, Xuchun Li, Bryan Wang
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Separation.Connected
/-!
# Existence of an open normal subgroup in any clopen neighborhood of the neutral element

This file proves the lemma `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`,
which states that in a compact topological group, for any clopen neighborhood of 1,
there exists an open normal subgroup contained within it.

We then apply this lemma to show `ProfiniteGrp.closedSubgroup_eq_sInf_open`:
any closed subgroup of a profinite group is the intersection of the open subgroups containing it.

This file is split out from the file `OpenSubgroup` because it needs more imports.
-/

public section

namespace IsTopologicalGroup

theorem exist_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  rcases exist_openSubgroup_sub_clopen_nhds_of_one WClopen einW with ⟨H, hH⟩
  have : Subgroup.FiniteIndex H.toSubgroup := H.finiteIndex_of_finite_quotient
  use { toSubgroup := Subgroup.normalCore H
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed H.isClosed) }
  exact fun _ b ↦ hH (H.normalCore_le b)

end IsTopologicalGroup

namespace ProfiniteGrp

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exist_openNormalSubgroup_sub_open_nhds_of_one
    {U : Set G} (UOpen : IsOpen U) (einU : 1 ∈ U) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
  rcases IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW.2 hW.1 with ⟨H, hH⟩
  exact ⟨H, fun _ a ↦ h (hH a)⟩

open scoped Pointwise in
/--
Any closed subgroup of a profinite group is the intersection of the open subgroups containing it.
See https://math.stackexchange.com/questions/5023433/closed-subgroups-of-a-compact-topological-group.
-/
theorem closedSubgroup_eq_sInf_open (H : ClosedSubgroup G) :
    H = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := by
  apply le_antisymm
  · exact le_sInf fun N hN ↦ hN.2
  · intro g hg
    by_contra hg_not
    let U : Set G := (g • H)ᶜ
    have UOpen : IsOpen U :=
      ((Homeomorph.mulLeft g).isClosedMap _ H.isClosed').isOpen_compl
    have einU : 1 ∈ U := by
      refine Set.mem_compl (fun ⟨l, hl, (hgl : g * l = 1)⟩ ↦ ?_)
      rw [← inv_eq_iff_mul_eq_one] at hgl
      exact hg_not <| inv_mem_iff.mp (hgl ▸ hl)
    obtain ⟨N, hN⟩ := exist_openNormalSubgroup_sub_open_nhds_of_one UOpen einU
    let NH : Subgroup G := N ⊔ H
    have hg_not' : g ∉ NH := by
      by_contra hg'
      rcases Subgroup.mem_sup_of_normal_left.mp hg' with ⟨y, hy, z, hz, hyz⟩
      rw [← eq_mul_inv_iff_mul_eq] at hyz
      exact hN (hyz ▸ hy) <| mem_leftCoset g (inv_mem_iff.mpr hz)
    exact hg_not' <|
      Subgroup.mem_sInf.mp hg _ ⟨Subgroup.isOpen_mono le_sup_left N.isOpen, le_sup_right⟩

end ProfiniteGrp
