/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.MetricSpace.Bounded

/-! # The path component of the identity in a locally path connected topological group

This file defines the path component of the identity is an `OpenNormalSubgroup` when the ambient
topological group is locally path connected. We place this in a separate file to avoid importing
additional algebra into the topology hierarchy.
-/

@[expose] public section

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
