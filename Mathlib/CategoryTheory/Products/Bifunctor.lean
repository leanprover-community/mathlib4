/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathlib.CategoryTheory.Products.Basic

#align_import category_theory.products.bifunctor from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Lemmas about functors out of product categories.
-/


open CategoryTheory

namespace CategoryTheory.Bifunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

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
