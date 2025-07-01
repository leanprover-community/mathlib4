/-
Copyright (c) 2023 Andrea Laretto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Laretto
-/
import Mathlib.CategoryTheory.Products.Bifunctor

/-!
# Dinatural transformations

Dinatural transformations are special kinds of transformations between
functors `F G : Cᵒᵖ × C ⥤ D` which depend both covariantly and contravariantly
on the same category (also known as difunctors).

A dinatural transformation is a family of morphisms given only on *the diagonal* of the two
functors, and is such that a certain naturality hexagon commutes.

Note that dinatural transformations cannot be composed with each other (since the outer
hexagon does not commute in general), but can still be "pre/post-composed" with
ordinary natural transformations.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open Opposite Bifunctor
open scoped Prod

/-- Dinatural transformations between two (di)functors. -/
structure DinatTrans (F G : Cᵒᵖ × C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app (X : C) : F.obj ⟨op X, X⟩ ⟶ G.obj ⟨op X, X⟩
  /-- The commutativity square for a given morphism. -/
  dinaturality {X Y : C} (f : X ⟶ Y) :
      F.map (f.op ×ₘ 𝟙 _) ≫ app X ≫ G.map (𝟙 (op _) ×ₘ f) =
      F.map (𝟙 (op _) ×ₘ f) ≫ app Y ≫ G.map (f.op ×ₘ 𝟙 _) :=
        by aesop_cat

attribute [reassoc (attr := simp)] DinatTrans.dinaturality

/-- Notation for dinatural transformations. -/
infixr:50 " ⤞ " => DinatTrans

/-- Opposite of a difunctor. -/
@[simps!]
def Functor.diop (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ × C ⥤ Dᵒᵖ :=
  prod (𝟭 Cᵒᵖ) (opOp C) ⋙ flip (biop F)

variable {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]

variable {F G H : Cᵒᵖ × C ⥤ D}

/-- Post-composition with a natural transformation. -/
@[simps]
def DinatTrans.compNatTrans (δ : F ⤞ G) (α : G ⟶ H) : F ⤞ H where
  app X := δ.app X ≫ α.app (op X, X)
  dinaturality f := by simp; rw [←α.naturality, reassoc_of% δ.dinaturality f,←α.naturality]

/-- Pre-composition with a natural transformation. -/
@[simps]
def DinatTrans.precompNatTrans (δ : G ⤞ H) (α : F ⟶ G) : F ⤞ H where
  app X := α.app (op X, X) ≫ δ.app X
  dinaturality {X Y} f := by simp only [Category.assoc, NatTrans.naturality_assoc, dinaturality]

/-- Opposite of a dinatural transformation. -/
@[simps]
def DinatTrans.op (α : F ⤞ G) : G.diop ⤞ F.diop where
  app X := by simp; exact (α.app X).op
  dinaturality f := Quiver.Hom.unop_inj <| by
    convert α.dinaturality f using 1 <;> exact Category.assoc _ _ _

end CategoryTheory
