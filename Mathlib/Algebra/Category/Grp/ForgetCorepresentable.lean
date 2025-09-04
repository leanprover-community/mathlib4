/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrp.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrp`, `AddGrp`
and `Grp`.

-/

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

namespace MonoidHom

end MonoidHom

namespace AddMonoidHom

end AddMonoidHom

/-- The forget functor `Grp.{u} ⥤ Type u` is corepresentable. -/
def Grp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget Grp.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `CommGrp.{u} ⥤ Type u` is corepresentable. -/
def CommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrp.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `AddGrp.{u} ⥤ Type u` is corepresentable. -/
def AddGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrp.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

/-- The forget functor `AddCommGrp.{u} ⥤ Type u` is corepresentable. -/
def AddCommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrp.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

instance Grp.forget_isCorepresentable :
    (forget Grp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' Grp.coyonedaObjIsoForget

instance CommGrp.forget_isCorepresentable :
    (forget CommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrp.coyonedaObjIsoForget

instance AddGrp.forget_isCorepresentable :
    (forget AddGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrp.coyonedaObjIsoForget

instance AddCommGrp.forget_isCorepresentable :
    (forget AddCommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrp.coyonedaObjIsoForget
