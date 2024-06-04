/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic

#align_import category_theory.category.Pointed from "leanprover-community/mathlib"@"c8ab806ef73c20cab1d87b5157e43a82c205f28e"

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `typeToPointed` to an equivalence
-/


open CategoryTheory

universe u

variable {α β : Type*}

/-- The category of pointed types. -/
structure Pointed : Type (u + 1) where
  /-- the underlying type -/
  X : Type u
  /-- the distinguished element -/
  point : X
set_option linter.uppercaseLean3 false in
#align Pointed Pointed

namespace Pointed

instance : CoeSort Pointed Type* :=
  ⟨X⟩

-- Porting note: protected attribute does not work
--attribute [protected] Pointed.X

/-- Turns a point into a pointed type. -/
def of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩
set_option linter.uppercaseLean3 false in
#align Pointed.of Pointed.of

@[simp]
theorem coe_of {X : Type*} (point : X) : ↥(of point) = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Pointed.coe_of Pointed.coe_of

alias _root_.Prod.Pointed := of
set_option linter.uppercaseLean3 false in
#align prod.Pointed Prod.Pointed

instance : Inhabited Pointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
protected structure Hom (X Y : Pointed.{u}) : Type u where
  /-- the underlying map -/
  toFun : X → Y
  /-- compatibility with the distinguished points -/
  map_point : toFun X.point = Y.point
set_option linter.uppercaseLean3 false in
#align Pointed.hom Pointed.Hom

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
def id (X : Pointed) : Pointed.Hom X X :=
  ⟨_root_.id, rfl⟩
set_option linter.uppercaseLean3 false in
#align Pointed.hom.id Pointed.Hom.id

instance (X : Pointed) : Inhabited (Pointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩
set_option linter.uppercaseLean3 false in
#align Pointed.hom.comp Pointed.Hom.comp

end Hom

instance largeCategory : LargeCategory Pointed where
  Hom := Pointed.Hom
  id := Hom.id
  comp := @Hom.comp
set_option linter.uppercaseLean3 false in
#align Pointed.large_category Pointed.largeCategory

@[simp] lemma Hom.id_toFun' (X : Pointed.{u}) : (𝟙 X : X ⟶ X).toFun = _root_.id := rfl

@[simp] lemma Hom.comp_toFun' {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

instance concreteCategory : ConcreteCategory Pointed where
  forget :=
    { obj := Pointed.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
set_option linter.uppercaseLean3 false in
#align Pointed.concrete_category Pointed.concreteCategory

/-- Constructs an isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β where
  hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext _ _ e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext _ _ e.self_comp_symm
set_option linter.uppercaseLean3 false in
#align Pointed.iso.mk Pointed.Iso.mk

end Pointed

/-- `Option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
def typeToPointed : Type u ⥤ Pointed.{u} where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext _ _ Option.map_id
  map_comp _ _ := Pointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
set_option linter.uppercaseLean3 false in
#align Type_to_Pointed typeToPointed

/-- `typeToPointed` is the free functor. -/
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => f.toFun ∘ Option.some
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl
          right_inv := fun f => funext fun _ => rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Pointed.Hom.ext
        funext x
        cases x <;> rfl }
set_option linter.uppercaseLean3 false in
#align Type_to_Pointed_forget_adjunction typeToPointedForgetAdjunction
