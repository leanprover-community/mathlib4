/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
import Mathlib.CategoryTheory.Products.Basic

/-!
# Lemmas about functors out of product categories.
-/


open CategoryTheory

namespace CategoryTheory.Bifunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

open scoped Prod

@[simp]
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map ((𝟙 X) ×ₘ (𝟙 Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)

@[simp]
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (𝟙 W ×ₘ (f ≫ g)) = F.map (𝟙 W ×ₘ f) ≫ F.map (𝟙 W ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]

@[simp]
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((f ≫ g) ×ₘ 𝟙 W) = F.map (f ×ₘ 𝟙 W) ≫ F.map (g ×ₘ 𝟙 W) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]

@[simp]
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (𝟙 X ×ₘ g) ≫ F.map (f ×ₘ 𝟙 Y') = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

@[simp]
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (f ×ₘ 𝟙 Y) ≫ F.map (𝟙 X' ×ₘ g) = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

end CategoryTheory.Bifunctor
