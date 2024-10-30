/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song, Xuchun Li
-/
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
/-!
# Open normal subgroup in a clopen neighborhood of One
This file defines `OpenNormalSubgroupSubClopenNhdsOfOne`, which strengthens the result of
`OpenSubgroupSubClopenNhdsOfOne` into open *normal* subgroups.

This file is split out from the file `OpenSubgroup` because the need of more imports.
-/

namespace TopologicalGroup

theorem existOpenNormalSubgroupSubClopenNhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  rcases existOpenSubgroupSubClopenNhdsOfOne WClopen einW with ⟨H, hH⟩
  letI : Subgroup.FiniteIndex H.1 := Subgroup.finiteIndex_of_finite_quotient H.1
  use { toSubgroup := Subgroup.normalCore H
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ <|
          Subgroup.normalCore_isClosed H.1 <| OpenSubgroup.isClosed H }
  exact fun _ b ↦ hH (Subgroup.normalCore_le H.1 b)

end TopologicalGroup
