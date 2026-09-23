/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrpCat`, `AddGrpCat`
and `GrpCat`.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℤ →+ G) ≃ G`

These universe-monomorphic variants of `zmultiplesHom`/`zpowersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- The equivalence `(ULift ℤ →+ G) ≃ G` for any additive group `G`. -/
@[simps!]
def uliftZMultiplesHom (G : Type u) [AddGroup G] : G ≃ (ULift.{u} ℤ →+ G) :=
  (zmultiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- The equivalence `(ULift (Multiplicative ℤ) →* G) ≃ G` for any group `G`. -/
@[simps!]
def uliftZPowersHom (G : Type u) [Group G] : G ≃ (ULift.{u} (Multiplicative ℤ) →* G) :=
  (zpowersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/-- The forget functor `GrpCat.{u} ⥤ Type u` is corepresentable. -/
def GrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget GrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `CommGrpCat.{u} ⥤ Type u` is corepresentable. -/
def CommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `AddGrpCat.{u} ⥤ Type u` is corepresentable. -/
def AddGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

/-- The forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable. -/
def AddCommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

instance GrpCat.forget_isCorepresentable :
    (forget GrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' GrpCat.coyonedaObjIsoForget

instance CommGrpCat.forget_isCorepresentable :
    (forget CommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrpCat.coyonedaObjIsoForget

instance AddGrpCat.forget_isCorepresentable :
    (forget AddGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrpCat.coyonedaObjIsoForget

instance AddCommGrpCat.forget_isCorepresentable :
    (forget AddCommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrpCat.coyonedaObjIsoForget
