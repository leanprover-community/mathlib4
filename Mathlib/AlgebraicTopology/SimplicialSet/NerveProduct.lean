/-
Copyright (c) 2026 Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennis Sweeney
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

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

/-- `nerve` preserves products. -/
def nerveProdIso : nerve (C₁ × C₂) ≅ nerve C₁ ⊗ nerve C₂ := by
  let app (n : SimplexCategoryᵒᵖ) := (ComposableArrows.prodEquiv C₁ C₂ n.unop.len).toIso
  exact NatIso.ofComponents app

/-- Map a nerve of a product category to product of the nerves. -/
def nerveProdToProdNerve : nerve (C₁ × C₂) ⟶ nerve C₁ ⊗ nerve C₂ := (nerveProdIso C₁ C₂).hom

/-- Map a product of nerves to the nerve of the product category. -/
def prodNerveToNerveProd : nerve C₁ ⊗ nerve C₂ ⟶ nerve (C₁ × C₂) := (nerveProdIso C₁ C₂).inv

end

section
variable {C₁ C₂ : Type u} [Category.{v} C₁] [Category.{v} C₂]
variable {D₁ D₂ : Type u} [Category.{v} D₁] [Category.{v} D₂]

lemma nerveOfProdMap_prod_nerveMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    prodNerveToNerveProd C₁ C₂ ≫ nerveMap (F₁.prod F₂) ≫ nerveProdToProdNerve D₁ D₂
    = nerveMap F₁ ⊗ₘ nerveMap F₂ := rfl

variable {E₁ E₂ : Type u} [Category.{v} E₁] [Category.{v} E₂]

lemma nerve_of_product_interchange (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (G₁ : D₁ ⥤ E₁) (G₂ : D₂ ⥤ E₂) :
    (nerveMap F₁ ⊗ₘ nerveMap F₂) ≫ (nerveMap G₁ ⊗ₘ nerveMap G₂)
    = nerveMap (F₁ ⋙ G₁) ⊗ₘ nerveMap (F₂ ⋙ G₂) := rfl
end

/-- The nerve of the terminal category is the terminal simplicial set. -/
def nerveOfTerminal : nerve (𝟙_ Cat.{v,u}) ≅ 𝟙_ SSet where
  hom := SemiCartesianMonoidalCategory.toUnit _
  inv := {
    app n := by
      repeat constructor
      intro _
      exact {
        obj _ := by repeat constructor
        map _ := by repeat constructor
      }
  }

instance : Functor.Monoidal nerveFunctor where
  ε := nerveOfTerminal.inv
  μ C₁ C₂ := prodNerveToNerveProd C₁ C₂
  η := nerveOfTerminal.hom
  δ C₁ C₂ := nerveProdToProdNerve C₁ C₂

end CategoryTheory.nerve
