/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `typeToPointed` to an equivalence
-/


open CategoryTheory

universe u

/-- The category of pointed types. -/
structure Pointed : Type (u + 1) where
  /-- the underlying type -/
  protected X : Type u
  /-- the distinguished element -/
  point : X

namespace Pointed

instance : CoeSort Pointed Type* :=
  ⟨Pointed.X⟩

/-- Turns a point into a pointed type. -/
abbrev of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩

theorem coe_of {X : Type*} (point : X) : ↥(of point) = X :=
  rfl

alias _root_.Prod.Pointed := of

instance : Inhabited Pointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
protected structure Hom (X Y : Pointed.{u}) : Type u where
  /-- the underlying map -/
  toFun : X → Y
  /-- compatibility with the distinguished points -/
  map_point : toFun X.point = Y.point

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
def id (X : Pointed) : Pointed.Hom X X :=
  ⟨_root_.id, rfl⟩

instance (X : Pointed) : Inhabited (Pointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩

end Hom

instance largeCategory : LargeCategory Pointed where
  Hom := Pointed.Hom
  id := Hom.id
  comp := @Hom.comp

@[simp] lemma Hom.id_toFun' (X : Pointed.{u}) : (𝟙 X : X ⟶ X).toFun = _root_.id := rfl

@[simp] lemma Hom.comp_toFun' {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

instance (X Y : Pointed) : FunLike { f : X → Y // f X.point = Y.point } X Y where
  coe f := f
  coe_injective' _ _ := Subtype.ext

instance hasForget : ConcreteCategory Pointed fun X Y ↦ { f : X → Y // f X.point = Y.point } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

/-- Constructs an isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β where
  hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm

end Pointed

/-- `Option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
def typeToPointed : Type u ⥤ Pointed.{u} where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
  map_comp _ _ := Pointed.Hom.ext (Option.map_comp_map _ _).symm

/-- `typeToPointed` is the free functor. -/
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ f.toFun ∘ Option.some
          invFun := fun f ↦ ⟨fun o ↦ o.elim Y.point f, rfl⟩
          left_inv := fun f ↦ by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply Pointed.Hom.ext
        funext x
        cases x <;> rfl }
