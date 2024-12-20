/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.Tactic.TFAE
import Mathlib.CategoryTheory.Distributive.Monoidal
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts


/-!

# Distributive categories

## Main definitions

A category `C` with finite products and finite coproducts is called (finitary) distributive if
the canonical distributivity isomorphism `X ⨯ (Y ⨿ Z) ⟶ (X ⨯ Y) ⨿ (X ⨯ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.


## Implementation Details

Given a category with chosen finite products, the cartesian monoidal structure is provided by the
instance `monoidalOfChosenFiniteProducts`. A cartesian distributive category is then defined as a
monoidal distributive category with respect to this monoidal structure.

Cartesian closed categories require a `ChosenFiniteProducts` instance.
If one whishes to state that a category that `hasFiniteProducts` is cartesian closed,
they should first promote the `hasFiniteProducts` instance to a `ChosenFiniteProducts` one using
`CategoryTheory.ChosenFiniteProducts.ofFiniteProducts`.


## Main results

- A monoidal category `C` tensor product is distributive if the tensor product preserves
  coproducts in each variable separately.


## References
- [J.R.B.Cockett, Introduction to distributive categories, 1992][]
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]
-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory MonoidalDistributive

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
[HasBinaryCoproducts C] [MonoidalLeftDistributive C]

attribute [local instance] monoidalOfHasFiniteProducts

attribute [local instance] MonoidalLeftDistributive.isoLeft


/-- The coproduct coprojections are monic in a distributive category. -/
instance [MonoidalLeftDistributive C]  : MonoCoprod C where
  binaryCofan_inl A B cocone hcolim := {
    right_cancellation := by
      intro Z f g he
      dsimp at f
      dsimp at g
      let u := inv (∂L Z A B)
      haveI : IsIso u := by exact IsIso.inv_isIso
      let q := (Z ◁ coprod.inl) ≫ u ≫ (coprod.desc (𝟙 _) (prod.fst ≫ prod.lift (𝟙 Z) f))
      have : q = 𝟙 _ := by
        unfold q
        rw [← assoc]
        simp [whisker_inl_comp_inv_distributor]
        --simp [coprod.inl_desc]




      --

  }








end CategoryTheory
