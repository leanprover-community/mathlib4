/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Laretto, Fernando Chu
-/
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

/-- Action of two-variable functors on morphisms. -/
@[simp]
def Functor.map₂ (F : C ⥤ D ⥤ E) {A B : C} {X Y : D} (f : A ⟶ B) (g : X ⟶ Y) :
    F.obj₂ A X ⟶ F.obj₂ B Y :=
  (F.map f).app X ≫ (F.obj B).map g

/-- Action of two-variable functors on a morphism in the left argument. -/
abbrev Functor.mapₗ (F : C ⥤ D ⥤ E) {A B : C} (f : A ⟶ B) (X : D) :
    F.obj₂ A X ⟶ F.obj₂ B X :=
  (F.map f).app X

@[simp, reassoc]
lemma Functor.mapₗ_comp (F : C ⥤ D ⥤ E) {A B T : C} (f : A ⟶ B) (g : B ⟶ T) (X : D) :
    F.mapₗ (f ≫ g) X = F.mapₗ f X ≫ F.mapₗ g X := by
  simp [Functor.mapₗ]

@[simp, reassoc]
lemma Functor.mapₗ_id (F : C ⥤ D ⥤ E) {A : C} (X : D) :
    F.mapₗ (𝟙 A) X = 𝟙 (F.obj₂ A X) := by
  simp [Functor.mapₗ]

/-- Action of two-variable functors on a morphism in the right argument. -/
abbrev Functor.mapᵣ (F : C ⥤ D ⥤ E) (A : C) {X Y : D} (g : X ⟶ Y) :
    F.obj₂ A X ⟶ F.obj₂ A Y :=
  (F.obj A).map g

/-- Apply a natural transformation between bifunctors to two objects. -/
@[simp]
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

end CategoryTheory
