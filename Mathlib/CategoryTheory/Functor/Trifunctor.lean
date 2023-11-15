/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Category
/-!
# Trifunctors obtained by composition of bifunctors

Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, we define
the trifunctor `bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃`.

Similarly, given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, we define
the trifunctor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `(F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)`.

-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₄] [Category C₁₂] [Category C₂₃]

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

/-- Auxiliary definition for `bifunctorComp₁₂`. -/
@[simps]
def bifunctorComp₁₂Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {X₃ Y₃} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

/-- Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
def bifunctorComp₁₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }

end

section

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)

/-- Auxiliary definition for `bifunctorComp₂₃`. -/
@[simps]
def bifunctorComp₂₃Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map := fun {X₃ Y₃} φ => (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality := fun {X₃ Y₃} φ => by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

/-- Given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
def bifunctorComp₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }

end

end CategoryTheory
