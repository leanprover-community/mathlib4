/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forgetful functor is corepresentable

The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable
by `ULift ℕ`. Similar results are obtained for the variants `CommMonCat`, `AddMonCat`
and `MonCat`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℕ →+ G) ≃ G`

These universe-monomorphic variants of `multiplesHom`/`powersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- Monoid homomorphisms from `ULift ℕ` are defined by the image of `1`. -/
@[simps!]
def uliftMultiplesHom (M : Type u) [AddMonoid M] : M ≃ (ULift.{u} ℕ →+ M) :=
  (multiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- Monoid homomorphisms from `ULift (Multiplicative ℕ)` are defined by the image
of `Multiplicative.ofAdd 1`. -/
@[simps!]
def uliftPowersHom (M : Type u) [Monoid M] : M ≃ (ULift.{u} (Multiplicative ℕ) →* M) :=
  (powersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/-- The forgetful functor `MonCat.{u} ⥤ Type u` is corepresentable. -/
def MonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget MonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso


/-- The forgetful functor `CommMonCat.{u} ⥤ Type u` is corepresentable. -/
def CommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget CommMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

/-- The forgetful functor `AddMonCat.{u} ⥤ Type u` is corepresentable. -/
def AddMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

/-- The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable. -/
def AddCommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddCommMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

instance MonCat.forget_isCorepresentable :
    (forget MonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget

instance CommMonCat.forget_isCorepresentable :
    (forget CommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget

instance AddMonCat.forget_isCorepresentable :
    (forget AddMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget

instance AddCommMonCat.forget_isCorepresentable :
    (forget AddCommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget
