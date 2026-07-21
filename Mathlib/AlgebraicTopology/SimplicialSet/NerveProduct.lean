/-
Copyright (c) 2026 Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennis Sweeney
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The nerve of a product category

The nerve of a product category can be identified with the product of the nerves.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory.nerve

section
variable (C₁ C₂ : Type u) [Category.{v} C₁] [Category.{v} C₂]

/-- Map a nerve of a product category to product of the nerves. -/
def nerveProdToProdNerve : nerve (C₁ × C₂) ⟶ (nerve C₁) ⊗ (nerve C₂) := by
  let app (n : SimplexCategoryᵒᵖ) : (nerve (C₁ × C₂)).obj n ⟶ (nerve C₁ ⊗ nerve C₂).obj n := by
    constructor
    exact ⟨fun γ ↦ ⟨γ ⋙ (CategoryTheory.Prod.fst C₁ C₂), γ ⋙ (CategoryTheory.Prod.snd C₁ C₂)⟩⟩
  constructor
  · intro m n d
    exact Eq.symm
          (CartesianMonoidalCategory.hom_ext (app m ≫ ((nerve C₁).map d ⊗ₘ (nerve C₂).map d))
            ((nerve (C₁ × C₂)).map d ≫ app n) rfl rfl)

/-- Map a product of nerves to the nerve of the product category. -/
def prodNerveToNerveProd : (nerve C₁) ⊗ (nerve C₂) ⟶ nerve (C₁ × C₂) := by
  let app (n : SimplexCategoryᵒᵖ) : (nerve C₁ ⊗ nerve C₂).obj n ⟶ (nerve (C₁ × C₂)).obj n := by
    constructor
    exact ⟨fun ⟨γ₁,γ₂⟩ ↦ γ₁.prod' γ₂⟩
  constructor
  · intro m n f
    exact Eq.symm (eq_of_comp_right_eq'
                    (app m ≫ (nerve (C₁ × C₂)).map f)
                    ((nerve C₁ ⊗ nerve C₂).map f ≫ app n)
                    rfl)

/-- nerve preserves products. -/
def nerveOfProductIso : nerve (C₁ × C₂) ≅ (nerve C₁) ⊗ (nerve C₂) where
  hom := nerveProdToProdNerve C₁ C₂
  inv := prodNerveToNerveProd C₁ C₂
end

section
variable {C₁ C₂ : Type u} [Category.{v} C₁] [Category.{v} C₂]
variable {D₁ D₂ : Type u} [Category.{v} D₁] [Category.{v} D₂]

/-- Convert a pair of functors to a map between products of nerves -/
def nerveOfProdMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (nerve C₁) ⊗ (nerve C₂) ⟶ (nerve D₁) ⊗ (nerve D₂) :=
  prodNerveToNerveProd C₁ C₂ ≫ nerveMap (F₁.prod F₂) ≫ nerveProdToProdNerve D₁ D₂

lemma nerveOfProdMap_prod_nerveMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    nerveOfProdMap F₁ F₂ = nerveMap F₁ ⊗ₘ nerveMap F₂ := rfl

variable {E₁ E₂ : Type u} [Category.{v} E₁] [Category.{v} E₂]

lemma nerve_of_product_interchange (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (G₁ : D₁ ⥤ E₁) (G₂ : D₂ ⥤ E₂) :
    (nerveOfProdMap F₁ F₂) ≫ (nerveOfProdMap G₁ G₂)
    = nerveOfProdMap (F₁ ⋙ G₁) (F₂ ⋙ G₂) := rfl
end

end CategoryTheory.nerve
