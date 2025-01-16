/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Distributive.Monoidal
import Mathlib.CategoryTheory.Limits.MonoCoprod


/-!

# Distributive categories

## Main definitions

A category `C` with finite products and binary coproducts is called distributive if the
canonical distributivity isomorphism `X ⨯ (Y ⨿ Z) ⟶ (X ⨯ Y) ⨿ (X ⨯ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.

## Implementation Details

Given a category with chosen finite products, the cartesian monoidal structure is provided by the
instance `monoidalOfChosenFiniteProducts`. A cartesian distributive category is then defined as a
monoidal distributive category with respect to this monoidal structure.

## Main results

- Cartesian distributive categories are both left and right distributive.

- The coproduct coprojections are monic in a cartesian distributive category.


## TODO

- Every cartesian distributive category is finitary distributive, meaning that
  the left tensor product functor `X ⊗ -` preserves all finite coproducts.

- Show that any extensive distributive category can be embedded into a topos.

## References

- [J.R.B.Cockett, Introduction to distributive categories, 1992][]
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]
-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory Distributive

variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteProducts

/-- A category `C` with finite products is cartesian distributive if is monoidal distributive
with respect to the cartesian monoidal structure. -/
abbrev CartesianDistribuitve :=
  IsMonoidalLeftDistrib C

attribute [local instance] symmetricOfHasFiniteProducts

/-- Every cartesian distributive category is both left and right distributive. -/
instance [CartesianDistribuitve C] : IsMonoidalDistrib C :=
  SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

/-- The coproduct coprojections are monic in a cartesian distributive category. -/
instance [IsMonoidalLeftDistrib C] : MonoCoprod C :=
  MonoCoprod.mk' fun A B => by
    refine ⟨BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ B) coprod.inr, ?_, ?_⟩
    · exact coprodIsCoprod A B
    · refine ⟨?_⟩
      intro Z f g he
      simp at he
      have : SplitMono (Z ◁ coprod.inl) := {
        retraction := (∂L Z A B).inv ≫ (coprod.desc (𝟙 _) (prod.fst ≫ prod.lift (𝟙 Z) f))
        id := by
          rw [← assoc]
          simp only [whiskerLeft_coprod_inl_leftDistrib_inv, coprod.inl_desc]
      }
      have : Mono (Z ◁ coprod.inl) := SplitMono.mono this
      have :  Mono (Z ◁ (coprod.inl (X:= A) (Y:= B))) := by infer_instance
      have H : (prod.lift (𝟙 Z) f) ≫ (Z ◁ coprod.inl (X:= A) (Y:= B)) =
        (prod.lift (𝟙 Z) g) ≫ (Z ◁ coprod.inl) := by
          simp
          simp_rw [he]
      have : (prod.lift (𝟙 Z) f) = (prod.lift (𝟙 Z) g) := by
        apply (cancel_mono  (Z ◁ (coprod.inl (X:= A) (Y:= B)))).1 H
      convert prod.lift_snd (𝟙 Z) g
      rw [← this]
      simp only [prod.lift_snd]

end CategoryTheory
