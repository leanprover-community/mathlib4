/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags

#align_import algebra.category.Group.equivalence_Group_AddGroup from "leanprover-community/mathlib"@"47b51515e69f59bca5cf34ef456e6000fe205a69"

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `Grp` and `AddGrp` by sending
  `X : Grp` to `Additive X` and `Y : AddGrp` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrp` and `AddCommGrp`
  by sending `X : CommGrp` to `Additive X` and `Y : AddCommGrp` to `Multiplicative Y`.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

namespace Grp

-- Porting note: Lean cannot find these now
private instance (X : Grp) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : CommGrp) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : AddGrp) : AddZeroClass X.α := X.str.toAddZeroClass
private instance (X : AddCommGrp) : AddZeroClass X.α := X.str.toAddZeroClass

/-- The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddGrp : Grp ⥤ AddGrp where
  obj X := AddGrp.of (Additive X)
  map {X} {Y} := MonoidHom.toAdditive
#align Group.to_AddGroup Grp.toAddGrp

end Grp

namespace CommGrp

/-- The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrp ⥤ AddCommGrp where
  obj X := AddCommGrp.of (Additive X)
  map {X} {Y} := MonoidHom.toAdditive
#align CommGroup.to_AddCommGroup CommGrp.toAddCommGrp

end CommGrp

namespace AddGrp

/-- The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toGrp : AddGrp ⥤ Grp where
  obj X := Grp.of (Multiplicative X)
  map {X} {Y} := AddMonoidHom.toMultiplicative
#align AddGroup.to_Group AddGrp.toGrp

end AddGrp

namespace AddCommGrp

/-- The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps]
def toCommGrp : AddCommGrp ⥤ CommGrp where
  obj X := CommGrp.of (Multiplicative X)
  map {X} {Y} := AddMonoidHom.toMultiplicative
#align AddCommGroup.to_CommGroup AddCommGrp.toCommGrp

end AddCommGrp

/-- The equivalence of categories between `Group` and `AddGroup`
-/
def groupAddGroupEquivalence : Grp ≌ AddGrp :=
  CategoryTheory.Equivalence.mk Grp.toAddGrp AddGrp.toGrp
    (NatIso.ofComponents fun X => MulEquiv.toGrpIso (MulEquiv.multiplicativeAdditive X))
    (NatIso.ofComponents fun X => AddEquiv.toAddGrpIso (AddEquiv.additiveMultiplicative X))
#align Group_AddGroup_equivalence groupAddGroupEquivalence

/-- The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
def commGroupAddCommGroupEquivalence : CommGrp ≌ AddCommGrp :=
  CategoryTheory.Equivalence.mk CommGrp.toAddCommGrp AddCommGrp.toCommGrp
    (NatIso.ofComponents fun X => MulEquiv.toCommGrpIso (MulEquiv.multiplicativeAdditive X))
    (NatIso.ofComponents fun X => AddEquiv.toAddCommGrpIso (AddEquiv.additiveMultiplicative X))
#align CommGroup_AddCommGroup_equivalence commGroupAddCommGroupEquivalence
