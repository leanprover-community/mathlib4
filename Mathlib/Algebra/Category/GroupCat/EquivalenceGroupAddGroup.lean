/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags

#align_import algebra.category.Group.equivalence_Group_AddGroup from "leanprover-community/mathlib"@"47b51515e69f59bca5cf34ef456e6000fe205a69"

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `GroupCat` and `AddGroupCat` by sending
  `X : GroupCat` to `Additive X` and `Y : AddGroupCat` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGroupCat` and `AddCommGroupCat`
  by sending `X : CommGroupCat` to `Additive X` and `Y : AddCommGroupCat` to `Multiplicative Y`.
-/

-- Porting note: everything is upper case
set_option linter.uppercaseLean3 false

open CategoryTheory

namespace GroupCat

-- Porting note: Lean cannot find these now
private instance (X : GroupCat) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : CommGroupCat) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : AddGroupCat) : AddZeroClass X.α := X.str.toAddZeroClass
private instance (X : AddCommGroupCat) : AddZeroClass X.α := X.str.toAddZeroClass

/-- The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddGroupCat : GroupCat ⥤ AddGroupCat where
  obj X := AddGroupCat.of (Additive X)
  map {X} {Y} := MonoidHom.toAdditive
#align Group.to_AddGroup GroupCat.toAddGroupCat

end GroupCat

namespace CommGroupCat

/-- The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGroupCat : CommGroupCat ⥤ AddCommGroupCat where
  obj X := AddCommGroupCat.of (Additive X)
  map {X} {Y} := MonoidHom.toAdditive
#align CommGroup.to_AddCommGroup CommGroupCat.toAddCommGroupCat

end CommGroupCat

namespace AddGroupCat

/-- The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toGroupCat : AddGroupCat ⥤ GroupCat where
  obj X := GroupCat.of (Multiplicative X)
  map {X} {Y} := AddMonoidHom.toMultiplicative
#align AddGroup.to_Group AddGroupCat.toGroupCat

end AddGroupCat

namespace AddCommGroupCat

/-- The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toCommGroupCat : AddCommGroupCat ⥤ CommGroupCat where
  obj X := CommGroupCat.of (Multiplicative X)
  map {X} {Y} := AddMonoidHom.toMultiplicative
#align AddCommGroup.to_CommGroup AddCommGroupCat.toCommGroupCat

end AddCommGroupCat

/-- The equivalence of categories between `Group` and `AddGroup`
-/
def groupAddGroupEquivalence : GroupCat ≌ AddGroupCat :=
  CategoryTheory.Equivalence.mk GroupCat.toAddGroupCat AddGroupCat.toGroupCat
    (NatIso.ofComponents fun X => MulEquiv.toGroupCatIso (MulEquiv.multiplicativeAdditive X))
    (NatIso.ofComponents fun X => AddEquiv.toAddGroupCatIso (AddEquiv.additiveMultiplicative X))
#align Group_AddGroup_equivalence groupAddGroupEquivalence

/-- The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
def commGroupAddCommGroupEquivalence : CommGroupCat ≌ AddCommGroupCat :=
  CategoryTheory.Equivalence.mk CommGroupCat.toAddCommGroupCat AddCommGroupCat.toCommGroupCat
    (NatIso.ofComponents fun X => MulEquiv.toCommGroupCatIso (MulEquiv.multiplicativeAdditive X))
    (NatIso.ofComponents fun X => AddEquiv.toAddCommGroupCatIso (AddEquiv.additiveMultiplicative X))
#align CommGroup_AddCommGroup_equivalence commGroupAddCommGroupEquivalence
