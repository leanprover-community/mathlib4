/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Pointed
! leanprover-community/mathlib commit c8ab806ef73c20cab1d87b5157e43a82c205f28e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `Type_to_Pointed` to an equivalence
-/


open CategoryTheory

universe u

variable {α β : Type _}

/-- The category of pointed types. -/
structure Pointed : Type (u + 1) where
  pt : Type u
  point : X
#align Pointed Pointed

namespace Pointed

instance : CoeSort Pointed (Type _) :=
  ⟨X⟩

attribute [protected] Pointed.X

/-- Turns a point into a pointed type. -/
def of {X : Type _} (point : X) : Pointed :=
  ⟨X, point⟩
#align Pointed.of Pointed.of

@[simp]
theorem coe_of {X : Type _} (point : X) : ↥(of point) = X :=
  rfl
#align Pointed.coe_of Pointed.coe_of

alias of ← _root_.prod.Pointed
#align prod.Pointed Prod.pointed

instance : Inhabited Pointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
protected structure Hom (X Y : Pointed.{u}) : Type u where
  toFun : X → Y
  map_point : to_fun X.point = Y.point
#align Pointed.hom Pointed.Hom

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
def id (X : Pointed) : Hom X X :=
  ⟨id, rfl⟩
#align Pointed.hom.id Pointed.Hom.id

instance (X : Pointed) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
def comp {X Y Z : Pointed.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩
#align Pointed.hom.comp Pointed.Hom.comp

end Hom

instance largeCategory : LargeCategory Pointed
    where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp
  id_comp' _ _ _ := Hom.ext _ _ rfl
  comp_id' _ _ _ := Hom.ext _ _ rfl
  assoc' _ _ _ _ _ _ _ := Hom.ext _ _ rfl
#align Pointed.large_category Pointed.largeCategory

instance concreteCategory : ConcreteCategory Pointed
    where
  forget :=
    { obj := Pointed.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
#align Pointed.concrete_category Pointed.concreteCategory

/-- Constructs a isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β
    where
  Hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id' := Pointed.Hom.ext _ _ e.symm_comp_self
  inv_hom_id' := Pointed.Hom.ext _ _ e.self_comp_symm
#align Pointed.iso.mk Pointed.Iso.mk

end Pointed

/-- `option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
def typeToPointed : Type u ⥤ Pointed.{u}
    where
  obj X := ⟨Option X, none⟩
  map X Y f := ⟨Option.map f, rfl⟩
  map_id' X := Pointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Pointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Type_to_Pointed typeToPointed

/-- `Type_to_Pointed` is the free functor. -/
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => f.toFun ∘ Option.some
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            ext
            cases x
            exact f.map_point.symm
            rfl
          right_inv := fun f => funext fun _ => rfl }
      homEquiv_naturality_left_symm := fun X' X Y f g =>
        by
        ext
        cases x <;> rfl }
#align Type_to_Pointed_forget_adjunction typeToPointedForgetAdjunction

