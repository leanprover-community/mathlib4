/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Twop
! leanprover-community/mathlib commit c8ab806ef73c20cab1d87b5157e43a82c205f28e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Data.TwoPointing

/-!
# The category of two-pointed types

This defines `Twop`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of two-pointed types. -/
structure Twop : Type (u + 1) where
  pt : Type u
  toTwoPointing : TwoPointing X
#align Twop Twop

namespace Twop

instance : CoeSort Twop (Type _) :=
  ⟨X⟩

attribute [protected] Twop.X

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type _} (to_two_pointing : TwoPointing X) : Twop :=
  ⟨X, to_two_pointing⟩
#align Twop.of Twop.of

@[simp]
theorem coe_of {X : Type _} (to_two_pointing : TwoPointing X) : ↥(of to_two_pointing) = X :=
  rfl
#align Twop.coe_of Twop.coe_of

alias of ← _root_.two_pointing.Twop
#align two_pointing.Twop TwoPointing.twop

instance : Inhabited Twop :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
def toBipointed (X : Twop) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed
#align Twop.to_Bipointed Twop.toBipointed

@[simp]
theorem coe_toBipointed (X : Twop) : ↥X.toBipointed = ↥X :=
  rfl
#align Twop.coe_to_Bipointed Twop.coe_toBipointed

instance largeCategory : LargeCategory Twop :=
  InducedCategory.category toBipointed
#align Twop.large_category Twop.largeCategory

instance concreteCategory : ConcreteCategory Twop :=
  InducedCategory.concreteCategory toBipointed
#align Twop.concrete_category Twop.concreteCategory

instance hasForgetToBipointed : HasForget₂ Twop Bipointed :=
  InducedCategory.hasForget₂ toBipointed
#align Twop.has_forget_to_Bipointed Twop.hasForgetToBipointed

/-- Swaps the pointed elements of a two-pointed type. `two_pointing.swap` as a functor. -/
@[simps]
def swap : Twop ⥤ Twop where
  obj X := ⟨X, X.toTwoPointing.symm⟩
  map X Y f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Twop.swap Twop.swap

/-- The equivalence between `Twop` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : Twop ≌ Twop :=
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
#align Twop.swap_equiv Twop.swapEquiv

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl
#align Twop.swap_equiv_symm Twop.swapEquiv_symm

end Twop

@[simp]
theorem twop_swap_comp_forget_to_bipointed :
    Twop.swap ⋙ forget₂ Twop Bipointed = forget₂ Twop Bipointed ⋙ Bipointed.swap :=
  rfl
#align Twop_swap_comp_forget_to_Bipointed twop_swap_comp_forget_to_bipointed

/-- The functor from `Pointed` to `Twop` which adds a second point. -/
@[simps]
def pointedToTwopFst : Pointed.{u} ⥤ Twop
    where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map X Y f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_fst pointedToTwopFst

/-- The functor from `Pointed` to `Twop` which adds a first point. -/
@[simps]
def pointedToTwopSnd : Pointed.{u} ⥤ Twop
    where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map X Y f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_snd pointedToTwopSnd

@[simp]
theorem pointedToTwopFst_comp_swap : pointedToTwopFst ⋙ Twop.swap = pointedToTwopSnd :=
  rfl
#align Pointed_to_Twop_fst_comp_swap pointedToTwopFst_comp_swap

@[simp]
theorem pointedToTwopSnd_comp_swap : pointedToTwopSnd ⋙ Twop.swap = pointedToTwopFst :=
  rfl
#align Pointed_to_Twop_snd_comp_swap pointedToTwopSnd_comp_swap

@[simp]
theorem pointedToTwopFst_comp_forget_to_bipointed :
    pointedToTwopFst ⋙ forget₂ Twop Bipointed = pointedToBipointedFst :=
  rfl
#align Pointed_to_Twop_fst_comp_forget_to_Bipointed pointedToTwopFst_comp_forget_to_bipointed

@[simp]
theorem pointedToTwopSnd_comp_forget_to_bipointed :
    pointedToTwopSnd ⋙ forget₂ Twop Bipointed = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Twop_snd_comp_forget_to_Bipointed pointedToTwopSnd_comp_forget_to_bipointed

/-- Adding a second point is left adjoint to forgetting the second point. -/
def pointedToTwopFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwopFst ⊣ forget₂ Twop Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
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
#align Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction pointedToTwopFstForgetCompBipointedToPointedFstAdjunction

/-- Adding a first point is left adjoint to forgetting the first point. -/
def pointedToTwopSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwopSnd ⊣ forget₂ Twop Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
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
#align Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction pointedToTwopSndForgetCompBipointedToPointedSndAdjunction

