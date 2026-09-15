/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions with a parameter

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
this file introduces the notation `F ⊣₂ G` for the adjunctions
with a parameter (in `C₁`) between `F` and `G`.

(See `MonoidalClosed.internalHomAdjunction₂` in the file
`CategoryTheory.Closed.Monoidal` for an example of such an adjunction.)

Note: this notion is weaker than the notion of
"adjunction of two variables" which appears in the mathematical literature.
In order to have an adjunction of two variables, we need
a third functor `H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁` and two adjunctions with
a parameter `F ⊣₂ G` and `F.flip ⊣₂ H`.

## TODO

Show that given `F : C₁ ⥤ C₂ ⥤ C₃`, if `F.obj X₁` has a right adjoint
`G X₁ : C₃ ⥤ C₂` for any `X₁ : C₁`, then `G` extends as a
bifunctor `G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` with `F ⊣₂ G'` (and similarly for
left adjoints).

## References
* https://ncatlab.org/nlab/show/two-variable+adjunction

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

/-- Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
an adjunction with parameter `F ⊣₂ G` consists of the data of
adjunctions `F.obj X₁ ⊣ G.obj (op X₁)` for all `X₁ : C₁` which
satisfy a naturality condition with respect to `X₁`. -/
structure ParametrizedAdjunction where
  /-- a family of adjunctions -/
  adj (X₁ : C₁) : F.obj X₁ ⊣ G.obj (op X₁)
  unit_whiskerRight_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    (adj X₁).unit ≫ whiskerRight (F.map f) _ = (adj Y₁).unit ≫ whiskerLeft _ (G.map f.op) := by
      cat_disch

/-- The notation `F ⊣₂ G` stands for `ParametrizedAdjunction F G`
representing that the bifunctor `F` is the left adjoint to `G`
in an adjunction with a parameter. -/
infixl:15 " ⊣₂ " => ParametrizedAdjunction

namespace ParametrizedAdjunction

attribute [reassoc] unit_whiskerRight_map

variable {F G}

set_option backward.defeqAttrib.useBackward true in
/-- Alternative constructor for parametrized adjunctions, for which
the compatibility is stated in terms of `Adjunction.homEquiv`. -/
@[simps]
def mk' (adj : ∀ (X₁ : C₁), F.obj X₁ ⊣ G.obj (op X₁))
    (h : ∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) {X₂ : C₂} {X₃ : C₃} (g : (F.obj Y₁).obj X₂ ⟶ X₃),
      (adj X₁).homEquiv X₂ X₃ ((F.map f).app X₂ ≫ g) =
        (adj Y₁).homEquiv X₂ X₃ g ≫ (G.map f.op).app X₃ := by cat_disch) :
    F ⊣₂ G where
  adj := adj
  unit_whiskerRight_map {X₁ Y₁} f := by
    ext X₂
    simpa [Adjunction.homEquiv_unit] using h f (X₂ := X₂) (𝟙 _)

variable (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {X₃ Y₃ : C₃}

/-- The bijection `((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)`
given by an adjunction with a parameter `adj₂ : F ⊣₂ G`. -/
def homEquiv : ((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃) :=
  (adj₂.adj X₁).homEquiv _ _

lemma homEquiv_eq : adj₂.homEquiv = (adj₂.adj X₁).homEquiv X₂ X₃ := rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma homEquiv_naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) :
    adj₂.homEquiv ((F.map f₁).app X₂ ≫ g) =
      adj₂.homEquiv g ≫ (G.map f₁.op).app X₃ := by
  have := congr($(adj₂.unit_whiskerRight_map f₁).app X₂)
  dsimp at this
  simp only [homEquiv_eq, Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp,
    Category.assoc, NatTrans.naturality, reassoc_of% this]

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

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma whiskerLeft_map_counit {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    whiskerLeft _ (F.map f) ≫ (adj₂.adj Y₁).counit =
      whiskerRight (G.map f.op) _ ≫ (adj₂.adj X₁).counit := by
  ext X₃
  dsimp
  apply adj₂.homEquiv.injective
  rw [homEquiv_naturality_one, homEquiv_naturality_two]
  simp [homEquiv_eq, Adjunction.homEquiv_unit]

end ParametrizedAdjunction

end CategoryTheory
