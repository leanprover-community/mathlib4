/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
import Mathlib.CategoryTheory.Products.Basic

/-!
# Lemmas about functors out of product categories.
-/


open CategoryTheory Opposite

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]

namespace CategoryTheory.Bifunctor

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

/-- Opposite of a bifunctor -/
@[simps!]
def biop (F : C × D ⥤ E) : Cᵒᵖ × Dᵒᵖ ⥤ Eᵒᵖ :=
  (prodOpEquiv C).inverse ⋙ F.op

/-- Flipping of arguments of a bifunctor -/
@[simps!]
def flip (F : C × D ⥤ E) : D × C ⥤ E :=
  Prod.swap D C ⋙ F

end CategoryTheory.Bifunctor

namespace CategoryTheory.Functor

/-- Opposite of a bifunctor. -/
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

/- Natural transformations between functors with many variables. -/
namespace NatTrans

@[reassoc, simp]
lemma comp_app₂ {H G K : C ⥤ D ⥤ E} (α : H ⟶ G) (β : G ⟶ K) (X : C) (Y : D) :
    (α ≫ β).app₂ X Y = α.app₂ X Y ≫ β.app₂ X Y := rfl

@[reassoc, simp]
lemma comp_app₃ {H G K : C ⥤ D ⥤ E ⥤ F} (α : H ⟶ G) (β : G ⟶ K) (X : C) (Y : D)
    (Z : E) : (α ≫ β).app₃ X Y Z = α.app₃ X Y Z ≫ β.app₃ X Y Z := rfl

end NatTrans

end CategoryTheory
