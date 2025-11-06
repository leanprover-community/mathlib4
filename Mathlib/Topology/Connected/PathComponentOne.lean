/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.LocPathConnected

/-! # The path component of the identity in a locally path connected topological group

This file defines the path component of the identity is an `OpenNormalSubgroup` when the ambient
topological group is locally path connected. We place this in a separate file to avoid importing
additional algebra into the topology hierarchy.
-/

section PathComponentOne

variable (G : Type*) [TopologicalSpace G]

/-- The path component of the identity in a locally path connected topological group,
as an open normal subgroup. It is, in fact, clopen. -/
@[to_additive (attr := simps!)
/-- The path component of the identity in a locally path connected additive topological group,
as an open normal additive subgroup. It is, in fact, clopen. -/]
def OpenNormalSubgroup.pathComponentOne [Group G]
    [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    OpenNormalSubgroup G where
  toSubgroup := .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

namespace OpenNormalSubgroup

@[to_additive]
instance [Group G] [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    IsClosed (OpenNormalSubgroup.pathComponentOne G : Set G) :=
  .pathComponent 1

end OpenNormalSubgroup

end PathComponentOne
