/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Bipointed
! leanprover-community/mathlib commit c8ab806ef73c20cab1d87b5157e43a82c205f28e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Pointed

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/


open CategoryTheory

universe u

variable {α β : Type _}

/-- The category of bipointed types. -/
structure Bipointed : Type (u + 1) where
  pt : Type u
  toProd : X × X
#align Bipointed Bipointed

namespace Bipointed

instance : CoeSort Bipointed (Type _) :=
  ⟨X⟩

attribute [protected] Bipointed.X

/-- Turns a bipointing into a bipointed type. -/
def of {X : Type _} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩
#align Bipointed.of Bipointed.of

@[simp]
theorem coe_of {X : Type _} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl
#align Bipointed.coe_of Bipointed.coe_of

alias of ← _root_.prod.Bipointed
#align prod.Bipointed Prod.bipointed

instance : Inhabited Bipointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext]
protected structure Hom (X Y : Bipointed.{u}) : Type u where
  toFun : X → Y
  map_fst : to_fun X.toProd.1 = Y.toProd.1
  map_snd : to_fun X.toProd.2 = Y.toProd.2
#align Bipointed.hom Bipointed.Hom

namespace Hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps]
def id (X : Bipointed) : Hom X X :=
  ⟨id, rfl, rfl⟩
#align Bipointed.hom.id Bipointed.Hom.id

instance (X : Bipointed) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps]
def comp {X Y Z : Bipointed.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply, f.map_snd, g.map_snd]⟩
#align Bipointed.hom.comp Bipointed.Hom.comp

end Hom

instance largeCategory : LargeCategory Bipointed
    where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp
  id_comp' _ _ _ := Hom.ext _ _ rfl
  comp_id' _ _ _ := Hom.ext _ _ rfl
  assoc' _ _ _ _ _ _ _ := Hom.ext _ _ rfl
#align Bipointed.large_category Bipointed.largeCategory

instance concreteCategory : ConcreteCategory Bipointed
    where
  forget :=
    { obj := Bipointed.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
#align Bipointed.concrete_category Bipointed.concreteCategory

/-- Swaps the pointed elements of a bipointed type. `prod.swap` as a functor. -/
@[simps]
def swap : Bipointed ⥤ Bipointed where
  obj X := ⟨X, X.toProd.symm⟩
  map X Y f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Bipointed.swap Bipointed.swap

/-- The equivalence between `Bipointed` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : Bipointed ≌ Bipointed :=
  Equivalence.mk swap swap
    (NatIso.ofComponents
      (fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
    (NatIso.ofComponents
      (fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
#align Bipointed.swap_equiv Bipointed.swapEquiv

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl
#align Bipointed.swap_equiv_symm Bipointed.swapEquiv_symm

end Bipointed

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the second point. -/
def bipointedToPointedFst : Bipointed ⥤ Pointed
    where
  obj X := ⟨X, X.toProd.1⟩
  map X Y f := ⟨f.toFun, f.map_fst⟩
#align Bipointed_to_Pointed_fst bipointedToPointedFst

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the first point. -/
def bipointedToPointedSnd : Bipointed ⥤ Pointed
    where
  obj X := ⟨X, X.toProd.2⟩
  map X Y f := ⟨f.toFun, f.map_snd⟩
#align Bipointed_to_Pointed_snd bipointedToPointedSnd

@[simp]
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget Pointed = forget Bipointed :=
  rfl
#align Bipointed_to_Pointed_fst_comp_forget bipointedToPointedFst_comp_forget

@[simp]
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget Pointed = forget Bipointed :=
  rfl
#align Bipointed_to_Pointed_snd_comp_forget bipointedToPointedSnd_comp_forget

@[simp]
theorem swap_comp_bipointedToPointedFst :
    Bipointed.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl
#align swap_comp_Bipointed_to_Pointed_fst swap_comp_bipointedToPointedFst

@[simp]
theorem swap_comp_bipointedToPointedSnd :
    Bipointed.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl
#align swap_comp_Bipointed_to_Pointed_snd swap_comp_bipointedToPointedSnd

/-- The functor from `Pointed` to `Bipointed` which bipoints the point. -/
def pointedToBipointed : Pointed.{u} ⥤ Bipointed
    where
  obj X := ⟨X, X.point, X.point⟩
  map X Y f := ⟨f.toFun, f.map_point, f.map_point⟩
#align Pointed_to_Bipointed pointedToBipointed

/-- The functor from `Pointed` to `Bipointed` which adds a second point. -/
def pointedToBipointedFst : Pointed.{u} ⥤ Bipointed
    where
  obj X := ⟨Option X, X.point, none⟩
  map X Y f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Bipointed_fst pointedToBipointedFst

/-- The functor from `Pointed` to `Bipointed` which adds a first point. -/
def pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed
    where
  obj X := ⟨Option X, none, X.point⟩
  map X Y f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Bipointed_snd pointedToBipointedSnd

@[simp]
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ Bipointed.swap = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Bipointed_fst_comp_swap pointedToBipointedFst_comp_swap

@[simp]
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ Bipointed.swap = pointedToBipointedFst :=
  rfl
#align Pointed_to_Bipointed_snd_comp_swap pointedToBipointedSnd_comp_swap

/-- `Bipointed_to_Pointed_fst` is inverse to `Pointed_to_Bipointed`. -/
@[simps]
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩ })
    fun X Y f => rfl
#align Pointed_to_Bipointed_comp_Bipointed_to_Pointed_fst pointedToBipointedCompBipointedToPointedFst

/-- `Bipointed_to_Pointed_snd` is inverse to `Pointed_to_Bipointed`. -/
@[simps]
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩ })
    fun X Y f => rfl
#align Pointed_to_Bipointed_comp_Bipointed_to_Pointed_snd pointedToBipointedCompBipointedToPointedSnd

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_fst` and `Bipointed_to_Pointed_fst`.
-/
def pointedToBipointedFstBipointedToPointedFstAdjunction :
    pointedToBipointedFst ⊣ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext
            cases x
            exact f.map_snd.symm
            rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun X' X Y f g =>
        by
        ext
        cases x <;> rfl }
#align Pointed_to_Bipointed_fst_Bipointed_to_Pointed_fst_adjunction pointedToBipointedFstBipointedToPointedFstAdjunction

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_snd` and `Bipointed_to_Pointed_snd`.
-/
def pointedToBipointedSndBipointedToPointedSndAdjunction :
    pointedToBipointedSnd ⊣ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext
            cases x
            exact f.map_fst.symm
            rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun X' X Y f g =>
        by
        ext
        cases x <;> rfl }
#align Pointed_to_Bipointed_snd_Bipointed_to_Pointed_snd_adjunction pointedToBipointedSndBipointedToPointedSndAdjunction

