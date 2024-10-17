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

/-- The open normal subgroup contained in a clopen nhd of `1` in a compact topological group. -/
noncomputable def OpenNormalSubgroupSubClopenNhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {U : Set G}
    (UClopen : IsClopen U) (einU : 1 ∈ U) : OpenNormalSubgroup G :=
  let H := OpenSubgroupSubClopenNhdsOfOne UClopen einU
  letI : Subgroup.FiniteIndex H.1 := Subgroup.finiteIndex_of_finite_quotient H.1
  { toSubgroup := Subgroup.normalCore H
    isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ <|
      Subgroup.normalCore_isClosed H.1 <| OpenSubgroup.isClosed H }

theorem openNormalSubgroupSubClopenNhdsOfOne_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {U : Set G}
    (UClopen : IsClopen U) (einU : 1 ∈ U) :
    ((OpenNormalSubgroupSubClopenNhdsOfOne UClopen einU) : Set G) ⊆ U :=
    fun _ b ↦ openSubgroupSubClopenNhdsOfOne_spec UClopen einU
      (Subgroup.normalCore_le (OpenSubgroupSubClopenNhdsOfOne UClopen einU).1 b)

end TopologicalGroup
