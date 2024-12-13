/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.Tactic.TFAE


/-!

# Distributive categories

## Main definitions

A (finitary) distributive monoidal category is a monoidal category `C` with coproducts such that
the canonical distributivity isomorphism `(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.

## Main results

- A monoidal category `C` tensor product is distributive if the tensor product preserves
  coproducts in each variable separately.

## Monic coprojections
conjecture: In the case of semicartesian monoidal categories, the coprojections are monic.

## References
- when is a semicartesian monoidal category cartesian?
https://mathoverflow.net/questions/348480/a-semicartesian-monoidal-category-with-diagonals-is-cartesian-proof

-
-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

class TensorCoprodLeftDistrib [HasBinaryCoproducts C] where
  mor (X Y Z : C) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z) :=
    coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
  iso {X Y Z : C} : IsIso (mor X Y Z)

class TensorCoprodRightDistrib [HasBinaryCoproducts C] where
  mor (X Y Z : C) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X :=
    coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _)
  iso {X Y Z : C} : IsIso (mor X Y Z)

/-- In a symmetric monoidal category, if the tensor product is left distributive over coproducts
then it is right distributive over coproducts.-/
instance tensor_coprod_right_distrib_of_tensor_coprod_left_distrib
    [SymmetricCategory C] [HasBinaryCoproducts C] [TensorCoprodLeftDistrib C] :
  TensorCoprodRightDistrib C where
    mor (X Y Z : C) := coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _)
    iso {X Y Z} := sorry

attribute [instance] tensor_coprod_right_distrib_of_tensor_coprod_left_distrib

/-- A monoidal category is distributive if the tensor product is left and right distributive
over coproducts.-/
class MonoidalDistributive [HasBinaryCoproducts C] where
  left_distrib : TensorCoprodLeftDistrib C

/-- A closed monoidal category is distributive. -/
def leftDistribOfClosed [HasBinaryCoproducts C] [MonoidalClosed C] (X Y Z : C) :
  (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) where
    hom := coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
    inv := MonoidalClosed.uncurry
      (coprod.desc (MonoidalClosed.curry coprod.inl) (MonoidalClosed.curry coprod.inr))
    hom_inv_id := by
      ext
      · rw [coprod.inl_desc_assoc, comp_id, ← MonoidalClosed.uncurry_natural_left,
        coprod.inl_desc, MonoidalClosed.uncurry_curry]
      · rw [coprod.inr_desc_assoc, comp_id, ← MonoidalClosed.uncurry_natural_left,
        coprod.inr_desc, MonoidalClosed.uncurry_curry]
    inv_hom_id := by
      rw [← MonoidalClosed.uncurry_natural_right, ← MonoidalClosed.eq_curry_iff]
      ext
      · rw [coprod.inl_desc_assoc, ← MonoidalClosed.curry_natural_right,
        coprod.inl_desc, ← MonoidalClosed.curry_natural_left,
        comp_id]
      · rw [coprod.inr_desc_assoc, ← MonoidalClosed.curry_natural_right,
        coprod.inr_desc, ← MonoidalClosed.curry_natural_left,
        comp_id]

instance distributive_of_closed [HasBinaryCoproducts C] [MonoidalClosed C] : MonoidalDistributive C where
  left_distrib := {
    iso {X Y Z} := Iso.isIso_hom (leftDistribOfClosed C X Y Z)
  }

end CategoryTheory
