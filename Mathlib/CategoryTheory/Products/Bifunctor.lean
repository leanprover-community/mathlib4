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

@[simp]
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map (Prod.mkHom (𝟙 X) (𝟙 Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)

@[simp]
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (Prod.mkHom (𝟙 W) (f ≫ g)) =
      F.map (Prod.mkHom (𝟙 W) f) ≫ F.map (Prod.mkHom (𝟙 W) g) := by
  rw [← Functor.map_comp, Prod.mkHom_comp, Category.comp_id]

@[simp]
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (Prod.mkHom (f ≫ g) (𝟙 W)) =
      F.map (Prod.mkHom f (𝟙 W)) ≫ F.map (Prod.mkHom g (𝟙 W)) := by
  rw [← Functor.map_comp, Prod.mkHom_comp, Category.comp_id]

@[simp]
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (Prod.mkHom (𝟙 X) g) ≫ F.map (Prod.mkHom f (𝟙 Y')) =
      F.map (Prod.mkHom f g) := by
  rw [← Functor.map_comp, Prod.mkHom_comp, Category.id_comp, Category.comp_id]

@[simp]
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (Prod.mkHom f (𝟙 Y)) ≫ F.map (Prod.mkHom (𝟙 X') g) =
      F.map (Prod.mkHom f g) := by
  rw [← Functor.map_comp, Prod.mkHom_comp, Category.id_comp, Category.comp_id]

end CategoryTheory.Bifunctor
