/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity of quotient groups

This file characterizes when a quotient group is simple.

## Main results

* `Group.isSimpleGroup_of_isCoatom`: the quotient of a group by a normal coatom of the subgroup
  lattice is simple.
* `CommGroup.isSimpleGroup_iff_isCoatom`: a subgroup of a commutative group is a coatom in the
  subgroup lattice iff the quotient by it is simple.
-/

public section

/-- The quotient by a normal coatom is a simple group. -/
@[to_additive]
theorem Group.isSimpleGroup_of_isCoatom {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    (h : IsCoatom M) : IsSimpleGroup (G ⧸ M) := by
  have : IsSimpleOrder (Subgroup (G ⧸ M)) := by
    rwa [(QuotientGroup.comapMk'OrderIso M).isSimpleOrder_iff, Set.isSimpleOrder_Ici_iff_isCoatom]
  exact IsSimpleGroup.of_isSimpleOrder

/-- A subgroup of a commutative group is maximal (a coatom in the subgroup lattice) iff the quotient
by it is simple. Group analogue of `isSimpleModule_iff_isCoatom`. -/
@[to_additive /-- A subgroup of an additive commutative group is maximal (a coatom in the subgroup
lattice) iff the quotient by it is simple. Additive group analogue of
`isSimpleModule_iff_isCoatom`. -/]
theorem CommGroup.isSimpleGroup_iff_isCoatom {G : Type*} [CommGroup G] {M : Subgroup G} :
    IsSimpleGroup (G ⧸ M) ↔ IsCoatom M := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom,
    ← (QuotientGroup.comapMk'OrderIso M).isSimpleOrder_iff, isSimpleGroup_iff, isSimpleOrder_iff]
  simp [Subgroup.normal_of_isMulCommutative]
