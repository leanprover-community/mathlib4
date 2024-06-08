/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Andrea Laretto
-/
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.CategoryTheory.Opposites

#align_import category_theory.products.bifunctor from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Lemmas about functors out of product categories.
-/

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}

variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]

namespace CategoryTheory.Bifunctor

@[simp]
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map ((𝟙 X, 𝟙 Y) : (X, Y) ⟶ (X, Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)
#align category_theory.bifunctor.map_id CategoryTheory.Bifunctor.map_id

@[simp]
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((𝟙 W, f ≫ g) : (W, X) ⟶ (W, Z)) =
      F.map ((𝟙 W, f) : (W, X) ⟶ (W, Y)) ≫ F.map ((𝟙 W, g) : (W, Y) ⟶ (W, Z)) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]
#align category_theory.bifunctor.map_id_comp CategoryTheory.Bifunctor.map_id_comp

@[simp]
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((f ≫ g, 𝟙 W) : (X, W) ⟶ (Z, W)) =
      F.map ((f, 𝟙 W) : (X, W) ⟶ (Y, W)) ≫ F.map ((g, 𝟙 W) : (Y, W) ⟶ (Z, W)) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]
#align category_theory.bifunctor.map_comp_id CategoryTheory.Bifunctor.map_comp_id

@[simp]
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ F.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) =
      F.map ((f, g) : (X, Y) ⟶ (X', Y')) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
#align category_theory.bifunctor.diagonal CategoryTheory.Bifunctor.diagonal

@[simp]
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ F.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
      F.map ((f, g) : (X, Y) ⟶ (X', Y')) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
#align category_theory.bifunctor.diagonal' CategoryTheory.Bifunctor.diagonal'

end CategoryTheory.Bifunctor

namespace CategoryTheory.Functor

/-- Opposite of a bifunctor.
-/
@[simps!]
def biop (F : Cᵒᵖ ⥤ D ⥤ E) : C ⥤ Dᵒᵖ ⥤ Eᵒᵖ := F.rightOp ⋙ Functor.opHom _ _

end CategoryTheory.Functor

namespace CategoryTheory

variable {C₁ C₂ : C} {D₁ D₂ : D} {E₁ E₂ : E}

/-- Action of two-variable functors on objects. -/
abbrev Functor.obj₂ (H : C ⥤ D ⥤ E) (A : C) (B : D) : E := (H.obj A).obj B

/-- Action of three-variable functors on objects. -/
abbrev Functor.obj₃ (H : C ⥤ D ⥤ E ⥤ F) (A : C) (B : D) (C : E) : F :=
  ((H.obj A).obj B).obj C

/-- Apply a natural transformation between bifunctors to two objects. -/
abbrev NatTrans.app₂ {F G : C ⥤ D ⥤ E} (α : NatTrans F G) (X : C) (Y : D) :
    F.obj₂ X Y ⟶ G.obj₂ X Y :=
  (α.app X).app Y

/-- Apply a natural transformation between bifunctors in three variables to three objects. -/
abbrev NatTrans.app₃ {H G : C ⥤ D ⥤ E ⥤ F} (α : NatTrans H G) (X : C) (Y : D) (Z : E) :
    H.obj₃ X Y Z ⟶ G.obj₃ X Y Z :=
  ((α.app X).app Y).app Z

/-- Action of two-variable functors on morphisms. -/
abbrev Functor.map₂ (H : C ⥤ D ⥤ E) (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) :
    H.obj₂ C₁ D₁ ⟶ H.obj₂ C₂ D₂ :=
  (H.map f).app D₁ ≫ (H.obj C₂).map g

/-- Action of three-variable functors on morphisms. -/
abbrev Functor.map₃ (H : C ⥤ D ⥤ E ⥤ F) (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) (h : E₁ ⟶ E₂) :
    H.obj₃ C₁ D₁ E₁ ⟶ H.obj₃ C₂ D₂ E₂ :=
  (H.map f).app₂ D₁ E₁ ≫ ((H.obj C₂).map g).app E₁ ≫ (H.obj₂ C₂ D₂).map h

/- Natural transformations between functors with many variables. -/
namespace NatTrans

@[reassoc]
lemma comp_app₂ {H G K : C ⥤ D ⥤ E} (α : H ⟶ G) (β : G ⟶ K) (X : C) (Y : D) :
    (α ≫ β).app₂ X Y = α.app₂ X Y ≫ β.app₂ X Y :=
  by rw [app₂, comp_app, comp_app]

@[reassoc]
lemma comp_app₃ {H G K : C ⥤ D ⥤ E ⥤ F} (α : H ⟶ G) (β : G ⟶ K) (X : C) (Y : D)
    (Z : E) : (α ≫ β).app₃ X Y Z = α.app₃ X Y Z ≫ β.app₃ X Y Z := rfl

/- Naturality for natural transformations in two variables. -/
@[reassoc]
lemma naturality₂ {H G : C ⥤ D ⥤ E} (α : NatTrans H G) {X Y X' Y'} (f : X ⟶ X')
    (g : Y ⟶ Y') : H.map₂ f g ≫ α.app₂ X' Y' = α.app₂ X Y ≫ G.map₂ f g := by
  rw [Category.assoc, naturality, naturality_app_assoc]

@[reassoc]
theorem naturality_app_app {G H : C ⥤ D ⥤ E ⥤ F} (T : G ⟶ H) (Z : E) {X₁ Y₁ : C}
    {X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (G.map f).app₂ X₂ Z ≫ ((G.obj Y₁).map g).app Z ≫ T.app₃ Y₁ Y₂ Z =
      T.app₃ X₁ X₂ Z ≫ (H.map₂ f g).app Z := by
  rw [naturality_app, ← Category.assoc, ← comp_app₂,
    naturality, comp_app₂, Category.assoc]
  rfl

/- Naturality for natural transformations in three variables. -/
@[reassoc (attr := simp)]
lemma naturality₃ {H G : C ⥤ D ⥤ E ⥤ F} (α : H ⟶ G) {X Y Z X' Y' Z'}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    H.map₃ f g h ≫ α.app₃ X' Y' Z' = α.app₃ X Y Z ≫ G.map₃ f g h := by
  simp only [Category.assoc, comp_app, naturality, naturality_app_app_assoc]

end NatTrans

end CategoryTheory
