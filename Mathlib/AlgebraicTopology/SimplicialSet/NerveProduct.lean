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

/-- `nerve` preserves products. -/
def nerveProdIso (C₁ C₂ : Type u) [Category.{v} C₁] [Category.{v} C₂] :
    nerve (C₁ × C₂) ≅ nerve C₁ ⊗ nerve C₂ :=
  NatIso.ofComponents (fun n ↦ (ComposableArrows.prodEquiv C₁ C₂ n.unop.len).toIso)

section
variable {C₁ C₂ : Type u} [Category.{v} C₁] [Category.{v} C₂]
variable {D₁ D₂ : Type u} [Category.{v} D₁] [Category.{v} D₂]

lemma nerveOfProdMap_prod_nerveMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (nerveProdIso C₁ C₂).inv ≫ nerveMap (F₁.prod F₂) ≫ (nerveProdIso D₁ D₂).hom =
      nerveMap F₁ ⊗ₘ nerveMap F₂ := rfl

variable {E₁ E₂ : Type u} [Category.{v} E₁] [Category.{v} E₂]

lemma nerve_of_product_interchange (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (G₁ : D₁ ⥤ E₁) (G₂ : D₂ ⥤ E₂) :
    (nerveMap F₁ ⊗ₘ nerveMap F₂) ≫ (nerveMap G₁ ⊗ₘ nerveMap G₂) =
      nerveMap (F₁ ⋙ G₁) ⊗ₘ nerveMap (F₂ ⋙ G₂) := rfl

end

instance : Functor.Monoidal nerveFunctor where
  δ C₁ C₂ := (nerveProdIso C₁ C₂).hom
  μ C₁ C₂ := (nerveProdIso C₁ C₂).inv
  η := SemiCartesianMonoidalCategory.toUnit _
  ε.app _ := TypeCat.ofHom fun _ ↦
    { obj _ := ⟨⟨⟨⟩⟩⟩
      map _ := ⟨⟨⟨rfl⟩⟩⟩ }

end CategoryTheory.nerve
