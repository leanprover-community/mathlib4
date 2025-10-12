/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `GrpCat` and `AddGrpCat` by sending
  `X : GrpCat` to `Additive X` and `Y : AddGrpCat` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrpCat` and `AddCommGrpCat`
  by sending `X : CommGrpCat` to `Additive X` and `Y : AddCommGrpCat` to `Multiplicative Y`.
-/


open CategoryTheory

namespace GrpCat

/-- The functor `GrpCat ⥤ AddGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddGrp : GrpCat ⥤ AddGrpCat where
  obj X := AddGrpCat.of (Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

end GrpCat

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where
  obj X := AddCommGrpCat.of (Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

end CommGrpCat

namespace AddGrpCat

/-- The functor `AddGrpCat ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toGrp : AddGrpCat ⥤ GrpCat where
  obj X := GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

end AddGrpCat

namespace AddCommGrpCat

/-- The functor `AddCommGrpCat ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toCommGrp : AddCommGrpCat ⥤ CommGrpCat where
  obj X := CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

end AddCommGrpCat

/-- The equivalence of categories between `GrpCat` and `AddGrpCat`
-/
@[simps]
def groupAddGroupEquivalence : GrpCat ≌ AddGrpCat where
  functor := GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence of categories between `CommGrpCat` and `AddCommGrpCat`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrpCat where
  functor := CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
