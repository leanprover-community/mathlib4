/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions between bifunctors

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
this file introduces adjunctions `F ⊣₂ G`.

(See `MonoidalClosed.internalHomAdjunction₂` in the file
`CategoryTheory.Closed.Monoidal` for an example of such an adjunction.)

Note: this notion is weaker than the notion of
"adjunction of two variables" which appears in the mathematical literature.
In order to have an adjunction of two variables, we need
a third functor `H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁` and two adjunctions between
bifunctors `F ⊣₂ G` and `F.flip ⊣₂ H`.

## References
* https://ncatlab.org/nlab/show/two-variable+adjunction

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

/-- Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
an adjunction `F ⊣₂ G` consists of the data of adjunctions
`F.obj X₁ ⊣ G.obj (op X₁)` for all `X₁ : C₁` which
satisfy a naturality condition with respect to `X₁`. -/
structure Adjunction₂ where
  /-- a family of adjunctions -/
  adj (X₁ : C₁) : F.obj X₁ ⊣ G.obj (op X₁)
  naturality' {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) {X₂ : C₂} {X₃ : C₃}
    (g : (F.obj Y₁).obj X₂ ⟶ X₃) :
      (adj X₁).homEquiv X₂ X₃ ((F.map f).app X₂ ≫ g) =
        (adj Y₁).homEquiv X₂ X₃ g ≫ (G.map f.op).app X₃ := by aesop_cat


/-- The notation `F ⊣₂ G` stands for `Adjunction₂ F G`
representing that the bifunctor `F` is left adjoint to `G` -/
infixl:15 " ⊣₂ " => Adjunction₂

namespace Adjunction₂

variable {F G} (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {X₃ Y₃ : C₃}

/-- The bijection `((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)`
given by an adjunction of bifunctors `adj₂ : F ⊣₂ G`. -/
def homEquiv : ((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃) :=
  (adj₂.adj X₁).homEquiv _ _

lemma homEquiv_eq : adj₂.homEquiv = (adj₂.adj X₁).homEquiv X₂ X₃ := rfl

@[reassoc]
lemma homEquiv_naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) :
    adj₂.homEquiv ((F.map f₁).app X₂ ≫ g) =
      adj₂.homEquiv g ≫ (G.map f₁.op).app X₃ :=
  adj₂.naturality' _ _

@[reassoc]
lemma homEquiv_naturality_two (f₂ : X₂ ⟶ Y₂) (g : (F.obj X₁).obj Y₂ ⟶ X₃) :
    adj₂.homEquiv ((F.obj X₁).map f₂ ≫ g) = f₂ ≫ adj₂.homEquiv g :=
  (adj₂.adj X₁).homEquiv_naturality_left _ _

@[reassoc]
lemma homEquiv_naturality_three (f₃ : X₃ ⟶ Y₃) (g : (F.obj X₁).obj X₂ ⟶ X₃) :
    adj₂.homEquiv (g ≫ f₃) = adj₂.homEquiv g ≫ (G.obj (op X₁)).map f₃ :=
  (adj₂.adj X₁).homEquiv_naturality_right _ _

@[reassoc]
lemma homEquiv_symm_naturality_one
    (f₁ : X₁ ⟶ Y₁) (g : X₂ ⟶ (G.obj (op Y₁)).obj X₃) :
    adj₂.homEquiv.symm (g ≫ (G.map f₁.op).app X₃) =
      (F.map f₁).app X₂ ≫ adj₂.homEquiv.symm g :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_one])

@[reassoc]
lemma homEquiv_symm_naturality_two
    (f₂ : X₂ ⟶ Y₂) (g : Y₂ ⟶ (G.obj (op X₁)).obj X₃) :
    adj₂.homEquiv.symm (f₂ ≫ g) =
      (F.obj X₁).map f₂ ≫ adj₂.homEquiv.symm g :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_two])

@[reassoc]
lemma homEquiv_symm_naturality_three
    (f₃ : X₃ ⟶ Y₃) (g : X₂ ⟶ (G.obj (op X₁)).obj X₃) :
    adj₂.homEquiv.symm (g ≫ (G.obj (op X₁)).map f₃) =
      adj₂.homEquiv.symm g ≫ f₃ :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_three])

end Adjunction₂

end CategoryTheory
