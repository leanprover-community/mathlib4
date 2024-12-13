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

A category `C` with finite products and finite coproducts is called (finitary) distributive if the
canonical distributivity isomorphism `X ⨯ (Y ⨿ Z) ⟶ (X ⨯ Y) ⨿ (X ⨯ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.

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

open Category Limits

namespace Limits

variable {C : Type u} [Category.{v} C]

/-- `X` is preterminal if there is at most one morphism from any object to `X`. -/
abbrev IsPreTerminal (X : C) :=
  ∀ Y, Subsingleton (Y ⟶ X)

/-- `X` is preinitial if there is at most one morphism from `X` to any object. -/
abbrev IsPreInitial (X : C) :=
  ∀ Y, Subsingleton (X ⟶ Y)

/-- For a preinitial object `P` which has a coproduct with itself the left and right coprojections
are equal. -/
@[simp]
theorem preinitial_coproj_eq {P : C} [HasBinaryCoproduct P P] [IsPreInitial P] :
    (coprod.inl : P ⟶ P ⨿ P) = coprod.inr :=
  by
    apply Subsingleton.elim

/--
If a preinitial object `P` has a coproduct with itself then the left (resp. right)
coprojection induces an isomorphism `P ≅ P ⨿ P`.
-/
def preinitialCoprojIso {P : C} [HasBinaryCoproduct P P] [IsPreInitial P] :
    P ≅ P ⨿ P where
  hom := coprod.inl
  inv := coprod.desc (𝟙 P) (𝟙 P)
  hom_inv_id := by
    symm
    apply Subsingleton.elim
  inv_hom_id := by
    ext
    · simp only [← assoc _ _ _, coprod.inl_desc, comp_id, id_comp]
    · simp only [← assoc _ _ _, coprod.inr_desc, comp_id, id_comp, preinitial_coproj_eq]

/-- An object `P` which has a coproduct with itself is preinitial if and only if the left
coprojection `P ⟶ P ⨿ P` is an isomorphism. -/
theorem preinitial_iff_coproj_is_iso {P : C} [HasBinaryCoproduct P P] :
    IsPreInitial P ↔ IsIso (coprod.inl : P ⟶ P ⨿ P) :=
  by
    constructor
    · intro
      exact Iso.isIso_hom (preinitialCoprojIso)
    · intro hiso
      obtain ⟨inv, hom_inv_id, inv_hom_id⟩ := hiso
      sorry

/--
In a category with coproducts, the following are equivalent:
1. `P` is preinitial.
2. for any map `P ⟶ X` the coprojection `X ⟶ X ⨿ P` is an isomorphism.
3. The coprojection `P ⟶ P ⨿ P` is an isomorphism.
-/
theorem preinitial_coprod_tfae [HasBinaryCoproducts C] (P : C) :
  List.TFAE [
      IsPreInitial P,
      ∀ X, IsIso (coprod.inl : X ⟶ X ⨿ P),
      IsIso (coprod.inl : P ⟶ P ⨿ P)] :=
  by
    sorry


end Limits

namespace MonoidalCategory

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
class Distributive [HasBinaryCoproducts C] where
  left_distrib : TensorCoprodLeftDistrib C

namespace Distributive




/-- In any distributive category, coproduct coprojections are monic. -/
theorem mono_coprod_inl [HasBinaryCoproducts C] [Distributive C] {X Y : C} :
    Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  by
    refine ⟨?_⟩
    intro Z f g h
    sorry



end Distributive




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

/-- A closed monoidal category is distributive. -/
instance distributive_of_closed [HasBinaryCoproducts C] [MonoidalClosed C] : Distributive C where
  left_distrib := {
    iso {X Y Z} := Iso.isIso_hom (leftDistribOfClosed C X Y Z)
  }





end MonoidalCategory

end CategoryTheory
