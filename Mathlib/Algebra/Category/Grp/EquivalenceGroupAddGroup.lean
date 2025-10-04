/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `GrpCat` and `AddGrp` by sending
  `X : GrpCat` to `Additive X` and `Y : AddGrp` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrpCat` and `AddCommGrp`
  by sending `X : CommGrpCat` to `Additive X` and `Y : AddCommGrp` to `Multiplicative Y`.
-/


open CategoryTheory

namespace GrpCat

/-- The functor `GrpCat ⥤ AddGrp` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddGrp : GrpCat ⥤ AddGrp where
  obj X := AddGrp.of (Additive X)
  map {_} {_} f := AddGrp.ofHom f.hom.toAdditive

end GrpCat

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrp` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrpCat ⥤ AddCommGrp where
  obj X := AddCommGrp.of (Additive X)
  map {_} {_} f := AddCommGrp.ofHom f.hom.toAdditive

end CommGrpCat

namespace AddGrp

/-- The functor `AddGrp ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toGrp : AddGrp ⥤ GrpCat where
  obj X := GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

end AddGrp

namespace AddCommGrp

/-- The functor `AddCommGrp ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toCommGrp : AddCommGrp ⥤ CommGrpCat where
  obj X := CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

end AddCommGrp

/-- The equivalence of categories between `GrpCat` and `AddGrp`
-/
@[simps]
def groupAddGroupEquivalence : GrpCat ≌ AddGrp where
  functor := GrpCat.toAddGrp
  inverse := AddGrp.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence of categories between `CommGrpCat` and `AddCommGrp`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrp where
  functor := CommGrpCat.toAddCommGrp
  inverse := AddCommGrp.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
