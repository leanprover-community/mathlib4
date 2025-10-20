/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrpCat`, `AddGrpCat`
and `GrpCat`.

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

/-- The equivalence `(Multiplicative ℤ →* α) ≃ α` for any group `α`. -/
@[deprecated zpowersHom (since := "2025-05-11")]
def fromMultiplicativeIntEquiv (α : Type u) [Group α] : (Multiplicative ℤ →* α) ≃ α :=
  (zpowersHom _).symm

/-- The equivalence `(ULift (Multiplicative ℤ) →* α) ≃ α` for any group `α`. -/
@[deprecated uliftZPowersHom (since := "2025-05-11")]
def fromULiftMultiplicativeIntEquiv (α : Type u) [Group α] :
    (ULift.{u} (Multiplicative ℤ) →* α) ≃ α :=
  (uliftZPowersHom _).symm

end MonoidHom

namespace AddMonoidHom

/-- The equivalence `(ℤ →+ α) ≃ α` for any additive group `α`. -/
@[deprecated zmultiplesHom (since := "2025-05-11")]
def fromIntEquiv (α : Type u) [AddGroup α] : (ℤ →+ α) ≃ α := (zmultiplesHom _).symm

/-- The equivalence `(ULift ℤ →+ α) ≃ α` for any additive group `α`. -/
@[deprecated uliftZMultiplesHom (since := "2025-05-11")]
def fromULiftIntEquiv (α : Type u) [AddGroup α] : (ULift.{u} ℤ →+ α) ≃ α :=
  (uliftZMultiplesHom _).symm

end AddMonoidHom

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
