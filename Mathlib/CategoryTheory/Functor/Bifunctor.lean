/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites

/-!
# Bifunctors

We develop some basic lemmas and APIs about (curried) bifunctors. See also
`CategoryTheory.Bifunctor`.
-/

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

namespace CategoryTheory

variable {C₁ C₂ : C} {D₁ D₂ : D} {E₁ E₂ : E}

/-- Action of two-variable functors on objects. -/
abbrev Functor.obj₂ (F : C ⥤ D ⥤ E) (A : C) (B : D) : E := (F.obj A).obj B

/-- Action of two-variable functors on objects. -/
@[simp]
def Functor.map₂ (F : C ⥤ D ⥤ E) {A B : C} {X Y : D} (f : A ⟶ B) (g : X ⟶ Y) :
    F.obj₂ A X ⟶ F.obj₂ B Y :=
  (F.map f).app X ≫ (F.obj B).map g

/-- Apply a natural transformation between bifunctors to two objects. -/
abbrev NatTrans.app₂ {F G : C ⥤ D ⥤ E} (α : F ⟶ G) (X : C) (Y : D) :
    F.obj₂ X Y ⟶ G.obj₂ X Y :=
  (α.app X).app Y

@[reassoc, simp]
lemma NatTrans.comp_app₂ {H G K : C ⥤ D ⥤ E} (α : H ⟶ G) (β : G ⟶ K) (X : C) (Y : D) :
    (α ≫ β).app₂ X Y = α.app₂ X Y ≫ β.app₂ X Y := rfl

/-- Opposite of a bifunctor. -/
@[simps!]
def Functor.biop (F : Cᵒᵖ ⥤ D ⥤ E) : C ⥤ Dᵒᵖ ⥤ Eᵒᵖ := F.rightOp ⋙ Functor.opHom _ _

/-- Opposite of a difunctor. -/
abbrev Functor.diop (F : Cᵒᵖ ⥤ C ⥤ D) : Cᵒᵖ ⥤ C ⥤ Dᵒᵖ := F.biop.flip

@[simp]
theorem map_id' (F : C ⥤ D ⥤ E) (X : C) (Y : D) :
    F.map₂ (𝟙 X) (𝟙 Y) = 𝟙 (F.obj₂ X Y) := by simp

@[simp]
theorem map_id (F : C ⥤ D ⥤ E) (X : C) (Y : D) :
    F.map₂ (𝟙 X) (𝟙 Y) = 𝟙 (F.obj₂ X Y) := by simp

@[simp]
theorem map_id_comp (F : C ⥤ D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map₂ (𝟙 W) (f ≫ g) = F.map₂ (𝟙 W) f ≫ F.map₂ (𝟙 W) g := by simp

@[simp]
theorem map_comp_id (F : C ⥤ D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map₂ (f ≫ g) (𝟙 W) = F.map₂ f (𝟙 W) ≫ F.map₂ g (𝟙 W) := by simp

@[simp]
theorem diagonal (F : C ⥤ D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map₂ (𝟙 X) g ≫ F.map₂ f (𝟙 Y') = F.map₂ f g := by simp

@[simp]
theorem diagonal' (F : C ⥤ D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map₂ f (𝟙 Y) ≫ F.map₂ (𝟙 X') g = F.map₂ f g := by simp

end CategoryTheory
