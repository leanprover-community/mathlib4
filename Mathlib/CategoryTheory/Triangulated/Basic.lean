/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Mathlib.Data.Int.Basic
import Mathlib.CategoryTheory.Shift.Basic

#align_import category_theory.triangulated.basic from "leanprover-community/mathlib"@"6876fa15e3158ff3e4a4e2af1fb6e1945c6e8803"

/-!
# Triangles

This file contains the definition of triangles in an additive category with an additive shift.
It also defines morphisms between these triangles.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
-/


noncomputable section

open CategoryTheory Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

/-
We work in a category `C` equipped with a shift.
-/
variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

/-- A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
See <https://stacks.math.columbia.edu/tag/0144>.
-/
structure Triangle where mk' ::
  /-- the first object of a triangle -/
  obj₁ : C
  /-- the second object of a triangle -/
  obj₂ : C
  /-- the third object of a triangle -/
  obj₃ : C
  /-- the first morphism of a triangle -/
  mor₁ : obj₁ ⟶ obj₂
  /-- the second morphism of a triangle -/
  mor₂ : obj₂ ⟶ obj₃
  /-- the third morphism of a triangle -/
  mor₃ : obj₃ ⟶ obj₁⟦(1 : ℤ)⟧
#align category_theory.pretriangulated.triangle CategoryTheory.Pretriangulated.Triangle

variable {C}

/-- A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
def Triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle C
    where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h
#align category_theory.pretriangulated.triangle.mk CategoryTheory.Pretriangulated.Triangle.mk

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

instance : Inhabited (Triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps!]
def contractibleTriangle (X : C) : Triangle C :=
  Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0
#align category_theory.pretriangulated.contractible_triangle CategoryTheory.Pretriangulated.contractibleTriangle

end

/-- A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f      g      h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧'
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f'     g'     h'
```
See <https://stacks.math.columbia.edu/tag/0144>.
-/
@[ext]
structure TriangleMorphism (T₁ : Triangle C) (T₂ : Triangle C) where
  /-- the first morphism in a triangle morphism -/
  hom₁ : T₁.obj₁ ⟶ T₂.obj₁
  /-- the second morphism in a triangle morphism -/
  hom₂ : T₁.obj₂ ⟶ T₂.obj₂
  /-- the third morphism in a triangle morphism -/
  hom₃ : T₁.obj₃ ⟶ T₂.obj₃
  /-- the first commutative square of a triangle morphism -/
  comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁ := by aesop_cat
  /-- the second commutative square of a triangle morphism -/
  comm₂ : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂ := by aesop_cat
  /-- the third commutative square of a triangle morphism -/
  comm₃ : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃ := by aesop_cat
#align category_theory.pretriangulated.triangle_morphism CategoryTheory.Pretriangulated.TriangleMorphism

attribute [reassoc (attr := simp)] TriangleMorphism.comm₁ TriangleMorphism.comm₂
  TriangleMorphism.comm₃

/-- The identity triangle morphism.
-/
@[simps]
def triangleMorphismId (T : Triangle C) : TriangleMorphism T T
    where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃
#align category_theory.pretriangulated.triangle_morphism_id CategoryTheory.Pretriangulated.triangleMorphismId

instance (T : Triangle C) : Inhabited (TriangleMorphism T T) :=
  ⟨triangleMorphismId T⟩

variable {T₁ T₂ T₃ : Triangle C}

/-- Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
    TriangleMorphism T₁ T₃ where
  hom₁ := f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃
#align category_theory.pretriangulated.triangle_morphism.comp CategoryTheory.Pretriangulated.TriangleMorphism.comp

/-- Triangles with triangle morphisms form a category.
-/
@[simps]
instance triangleCategory : Category (Triangle C)
    where
  Hom A B := TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g
#align category_theory.pretriangulated.triangle_category CategoryTheory.Pretriangulated.triangleCategory

@[ext]
lemma Triangle.hom_ext {A B : Triangle C} (f g : A ⟶ B)
  (h₁ : f.hom₁ = g.hom₁) (h₂ : f.hom₂ = g.hom₂) (h₃ : f.hom₃ = g.hom₃) : f = g :=
  TriangleMorphism.ext _ _ h₁ h₂ h₃

@[simps]
def Triangle.homMk (A B : Triangle C)
    (hom₁ : A.obj₁ ⟶ B.obj₁) (hom₂ : A.obj₂ ⟶ B.obj₂) (hom₃ : A.obj₃ ⟶ B.obj₃)
    (comm₁ : A.mor₁ ≫ hom₂ = hom₁ ≫ B.mor₁ := by aesop_cat)
    (comm₂ : A.mor₂ ≫ hom₃ = hom₂ ≫ B.mor₂ := by aesop_cat)
    (comm₃ : A.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ B.mor₃ := by aesop_cat) :
    A ⟶ B where
  hom₁ := hom₁
  hom₂ := hom₂
  hom₃ := hom₃
  comm₁ := comm₁
  comm₂ := comm₂
  comm₃ := comm₃
#align category_theory.pretriangulated.triangle.hom_mk CategoryTheory.Pretriangulated.Triangle.homMk

@[simps]
def Triangle.isoMk (A B : Triangle C)
    (iso₁ : A.obj₁ ≅ B.obj₁) (iso₂ : A.obj₂ ≅ B.obj₂) (iso₃ : A.obj₃ ≅ B.obj₃)
    (comm₁ : A.mor₁ ≫ iso₂.hom = iso₁.hom ≫ B.mor₁ := by aesop_cat)
    (comm₂ : A.mor₂ ≫ iso₃.hom = iso₂.hom ≫ B.mor₂ := by aesop_cat)
    (comm₃ : A.mor₃ ≫ iso₁.hom⟦1⟧' = iso₃.hom ≫ B.mor₃ := by aesop_cat) : A ≅ B where
  hom := Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : ℤ)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])
#align category_theory.pretriangulated.triangle.iso_mk CategoryTheory.Pretriangulated.Triangle.isoMk

lemma Triangle.eqToHom_hom₁ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₁ = eqToHom (by subst h; rfl) := by subst h; rfl
lemma Triangle.eqToHom_hom₂ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₂ = eqToHom (by subst h; rfl) := by subst h; rfl
lemma Triangle.eqToHom_hom₃ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₃ = eqToHom (by subst h; rfl) := by subst h; rfl

end CategoryTheory.Pretriangulated
