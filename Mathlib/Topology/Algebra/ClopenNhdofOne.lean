/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song, Xuchun Li
-/
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Separation.Profinite
/-!
# Existence of an open normal subgroup in any clopen neighborhood of the neutral element

This file proves the lemma `TopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhd_of_one`, which
states that in a compact topological group, for any clopen neighborhood of 1,
there exists an open normal subgroup contained within it.

This file is split out from the file `OpenSubgroup` because it needs more imports.
-/

namespace TopologicalGroup

theorem exist_openNormalSubgroup_sub_clopen_nhd_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  rcases exist_openSubgroup_sub_clopen_nhd_of_one WClopen einW with ⟨H, hH⟩
  have : Subgroup.FiniteIndex H.toSubgroup := H.finiteIndex_of_finite_quotient
  use { toSubgroup := Subgroup.normalCore H
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed H.isClosed) }
  exact fun _ b ↦ hH (H.normalCore_le b)

end TopologicalGroup

namespace ProfiniteGrp

theorem exist_openNormalSubgroup_sub_open_nhd_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) : ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
  rcases TopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhd_of_one hW.2 hW.1 with ⟨H, hH⟩
  exact ⟨H, fun _ a ↦ h (hH a)⟩

end ProfiniteGrp
