/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

@[expose] public section

namespace Mathlib.Tactic.CategoryTheory.Map

open CategoryTheory
open scoped CategoryTheory

@[reducible] def mapOppositeCategoryStruct {C : Type*} [CategoryTheory.Category C] :
    CategoryTheory.CategoryStruct Cᵒᵖ where
  comp f g := Quiver.Hom.op <|
    CategoryTheory.CategoryStruct.comp (Quiver.Hom.unop g) (Quiver.Hom.unop f)
  id X := Quiver.Hom.op <| CategoryTheory.CategoryStruct.id (Opposite.unop X)

local instance {C : Type*} [CategoryTheory.Category C] :
    CategoryTheory.CategoryStruct Cᵒᵖ := mapOppositeCategoryStruct (C := C)

instance (priority := low) oppositeCategoryStruct {C : Type*} [CategoryTheory.Category C] :
    CategoryTheory.CategoryStruct Cᵒᵖ :=
  mapOppositeCategoryStruct (C := C)

theorem mapUnop_id {C : Type*} [CategoryTheory.Category C] {X : Cᵒᵖ} :
    Quiver.Hom.unop (CategoryTheory.CategoryStruct.id X) =
      CategoryTheory.CategoryStruct.id (Opposite.unop X) :=
  rfl

theorem mapUnop_op {C : Type*} [CategoryTheory.Category C] {X Y : C} (f : X ⟶ Y) :
    Quiver.Hom.unop (Quiver.Hom.op f) = f :=
  rfl

theorem mapOp_unop {C : Type*} [CategoryTheory.Category C] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Quiver.Hom.op (Quiver.Hom.unop f) = f :=
  rfl

theorem mapOp_comp_unop {C : Type*} [CategoryTheory.Category C] {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Quiver.Hom.op
        (CategoryTheory.CategoryStruct.comp (Quiver.Hom.unop g) (Quiver.Hom.unop f)) =
      CategoryTheory.CategoryStruct.comp f g :=
  rfl

@[reducible] def mapOppositeCategory {C : Type*} [CategoryTheory.Category C] :
    CategoryTheory.Category Cᵒᵖ where
  __ := mapOppositeCategoryStruct (C := C)
  comp_id f := by
    rw [← mapOp_comp_unop, mapUnop_id, CategoryTheory.Category.id_comp, mapOp_unop]
  id_comp f := by
    rw [← mapOp_comp_unop, mapUnop_id, CategoryTheory.Category.comp_id, mapOp_unop]
  assoc f g h := by
    simp only [← mapOp_comp_unop, mapUnop_op, CategoryTheory.Category.assoc]

instance (priority := low) oppositeCategory {C : Type*} [CategoryTheory.Category C] :
    CategoryTheory.Category Cᵒᵖ :=
  mapOppositeCategory (C := C)

theorem mapOp_comp {C : Type*} [CategoryTheory.Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Quiver.Hom.op (CategoryTheory.CategoryStruct.comp f g) =
      @CategoryTheory.CategoryStruct.comp Cᵒᵖ
        (@CategoryTheory.Category.toCategoryStruct Cᵒᵖ (mapOppositeCategory (C := C)))
        _ _ _ (Quiver.Hom.op g) (Quiver.Hom.op f) :=
  rfl

theorem mapOp_id {C : Type*} [CategoryTheory.Category C] (X : C) :
    Quiver.Hom.op (CategoryTheory.CategoryStruct.id X) =
      @CategoryTheory.CategoryStruct.id Cᵒᵖ
        (@CategoryTheory.Category.toCategoryStruct Cᵒᵖ (mapOppositeCategory (C := C)))
        (Opposite.op X) :=
  rfl

theorem mapUnop_comp {C : Type*} [CategoryTheory.Category C] {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.CategoryStruct.comp f g).unop =
      CategoryTheory.CategoryStruct.comp (Quiver.Hom.unop g) (Quiver.Hom.unop f) := by
  rw [(mapOp_comp_unop f g).symm, mapUnop_op]

universe u1 u2 v1 v2

open Opposite

variable {C : Type u1} [CategoryTheory.Category.{v1} C] {D : Type u2}
  [CategoryTheory.Category.{v2} D]

/--
Opposite functor, definitional copy of `CategoryTheory.Functor.op` for specialized `@[map]` lemmas
without importing `Mathlib.CategoryTheory.Opposites`.
-/
@[reducible] def mapFunctorOp (F : CategoryTheory.Functor C D) :
    CategoryTheory.Functor (Opposite C) (Opposite D) where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op
  map_id X := by
    rw [mapUnop_id (X := X), F.map_id, mapOp_id]
  map_comp {X Y Z} f g := by
    rw [mapUnop_comp f g, F.map_comp, mapOp_comp]

end Mathlib.Tactic.CategoryTheory.Map
