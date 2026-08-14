/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.
-/

public section

open CategoryTheory

universe u

namespace ModuleCat

/-- The forgetful functor from `ℤ` modules to `AddCommGrpCat` admits an inverse. -/
@[expose] def intEquivalence : ModuleCat.{u} ℤ ≌ Ab.{u} where
  functor := forget₂ ..
  inverse :=
  { obj G := .of ℤ G
    map f := ModuleCat.ofHom f.hom.toIntLinearMap }
  unitIso := NatIso.ofComponents
    (fun G ↦ (AddEquiv.toIntLinearEquiv { __ := Equiv.refl G, map_add' _ _ := rfl }).toModuleIso)
    fun _ ↦ rfl
  counitIso := .refl _

instance forget₂AddCommGroupIsEquivalence : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).IsEquivalence :=
  intEquivalence.isEquivalence_functor

/-- The forgetful functor from `ℤ` modules to `AddCommGrpCat` is full. -/
instance forget₂_addCommGroup_full : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).Full :=
  inferInstance

/-- The forgetful functor from `ℤ` modules to `AddCommGrpCat` is essentially surjective. -/
instance forget₂_addCommGrp_essSurj : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).EssSurj :=
  inferInstance

end ModuleCat
