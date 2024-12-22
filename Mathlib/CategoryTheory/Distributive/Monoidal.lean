/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/


import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.End

/-!

# Distributive monoidal categories

## Main definitions

A monoidal category `C` with binary coproducts is distributive if the tensor product
preserves binary coproducts in each variable separately. More precisely, a
left distributive monoidal category is a monoidal category `C` with coproducts such that
the canonical left distributivity morphism (aka "left distributor")
`(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` is an isomorphism for all objects `X`, `Y`, and `Z` in `C`.

A right distributive monoidal category is a monoidal category `C` with
coproducts such that the canonical right distributivity morphism (aka "right distributor")
`(Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X` is an isomorphism for all objects `X`, `Y`, and `Z` in `C`.

A distributive monoidal category is a monoidal category that is both left and right distributive.

## Main results

- A symmetric monoidal category is left distributive if and only if it is right distributive.


## Examples

- A closed monoidal category is left distributive.

- For a category `C` the category of endofunctors `C ⥤ C` is left distributive, but almost
  never right distributive. The left distributivity is tentamount to the fact that the coproduct in
  the functor categories is computed pointwise.

- For a category `C` the category of finite-coproduct-preserving functors `C ⥤ C` is
  distributive.

## TODO

Show that a distributive monoidal category whose unit is weakly terminal is finitary distributive.

Provide more examples of the distributive monoidal structure on the following categories:

- The category of abelian groups with the monoidal structure given by the tensor product of
  abelian groups.
- The category of R-modules with the monoidal structure given by the tensor product of modules.
- The category of vector bundles over a topological space where the monoidal structure is given by
  the tensor product of vector bundles.
- The category of pointed types with the monoidal structure given by the smash product of
  pointed types and the coproduct given by the wedge sum.

## References

[Hans-Joachim Baues, Mamuka Jibladze, Andy Tonks, Cohomology of
 monoids in monoidal categories, in: Operads: Proceedings of Renaissance
 Conferences, Contemporary Mathematics 202, AMS (1997) 137-166][]

-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits Iso

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [HasBinaryCoproducts C]

/-- The canonical left distributivity morphism -/
def distributorLeft (X Y Z : C) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z) :=
  coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)

/-- The canonical right distributivity morphism -/
def distributorRight (X Y Z : C) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X :=
  coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _)

/-- Notation for the left distributor. -/
notation "∂L " => distributorLeft

/-- Notation for the right distributor. -/
notation "∂R " => distributorRight

@[reassoc (attr := simp)]
lemma coprod_inl_comp_distributorLeft {X Y Z : C} : coprod.inl ≫ (∂L X Y Z) = (X ◁ coprod.inl) :=
by
  rw [distributorLeft, coprod.inl_desc]

@[reassoc (attr := simp)]
lemma coprod_inr_comp_distributorLeft {X Y Z : C} : coprod.inr ≫ (∂L X Y Z) = (X ◁ coprod.inr) :=
by
  rw [distributorLeft, coprod.inr_desc]

@[reassoc (attr := simp)]
lemma coprod_inl_comp_distributorRight {X Y Z : C} : coprod.inl ≫ (∂R X Y Z) = (coprod.inl ▷ X) :=
by
  rw [distributorRight, coprod.inl_desc]

@[reassoc (attr := simp)]
lemma coprod_inr_comp_distributorRight {X Y Z : C} : coprod.inr ≫ (∂R X Y Z) = (coprod.inr ▷ X) :=
by
  rw [distributorRight, coprod.inr_desc]

/-- In a ymmetric monoidal category, the right distributor equals
the left distributor up to braidings. -/
@[reassoc (attr := simp)]
lemma right_distributor_braiding_left_distributor [SymmetricCategory C]
    {X Y Z : C} :
  ∂R X Y Z ≫ (β_ (Y ⨿ Z) X).hom = (coprod.map (β_ Y X).hom (β_ Z X).hom) ≫ ∂L X Y Z := by
    ext
    · simp
    · simp

@[reassoc (attr := simp)]
lemma left_distributor_braiding_right_distributor [SymmetricCategory C]
    {X Y Z : C} :
  ∂L X Y Z ≫ (β_ X (Y ⨿ Z)).hom = (coprod.map (β_ X Y).hom (β_ X Z).hom) ≫ ∂R X Y Z := by
    ext
    · simp
    · simp

variable (C)

/-- A monoidal category with binary coproducts is left distributive
if the left distributor is an isomorphism. -/
class MonoidalLeftDistributive where
  is_iso_distributorLeft {X Y Z : C} : IsIso (∂L X Y Z) := by infer_instance

/-- A monoidal category with binary coproducts is right distributive
if the right distributor is an isomorphism. -/
class MonoidalRightDistributive where
  is_iso_distributorRight {X Y Z : C} : IsIso (∂R X Y Z) := by infer_instance

/-- A monoidal category with binary coproducts is distributive
if it is both left and right distributive. -/
class MonoidalDistributive extends
  MonoidalLeftDistributive C, MonoidalRightDistributive C

namespace MonoidalDistributive

variable {C} [MonoidalLeftDistributive C]

attribute [local instance] MonoidalLeftDistributive.is_iso_distributorLeft

/-- The composite  `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`inv (∂L X Y Z) :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
equals the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[simp]
lemma whisker_inl_comp_inv_distributor
    {X Y Z : C} :
  (X ◁ coprod.inl) ≫ (inv (∂L X Y Z)) = coprod.inl := by
    apply (cancel_iso_hom_right _ _ (asIso <| ∂L X Y Z)).mp
    simp only [asIso_hom, assoc, IsIso.inv_hom_id, comp_id]
    rw [distributorLeft, coprod.inl_desc]

/-- In a distributive symmetric monoidal category, the right distributor is also an isomorphism. -/
instance right_distributor_iso [SymmetricCategory C]
    {X Y Z : C} :
  IsIso (∂R X Y Z) :=
    by
      refine ⟨?_⟩
      have : IsIso (∂L X Y Z) := by infer_instance
      obtain ⟨inv, hom_inv_id, inv_hom_id⟩ := this
      use (β_ (Y ⨿ Z) X).hom ≫  inv ≫ (coprod.map (β_ X Y).hom (β_ X Z).hom)
      constructor
      · slice_lhs 1 2 =>
          rw [right_distributor_braiding_left_distributor]
        slice_lhs 2 3 => rw [hom_inv_id]
        simp only [id_comp, coprod.map_map, SymmetricCategory.symmetry, coprod.map_id_id]
      · slice_lhs 3 4 =>
          rw [← left_distributor_braiding_right_distributor]
        slice_lhs 2 3 => rw [inv_hom_id]
        simp only [id_comp, coprod.map_map, SymmetricCategory.symmetry, coprod.map_id_id]

instance [SymmetricCategory C] : MonoidalDistributive C where

/-- A closed monoidal category is distributive. -/
def isoDistributorOfClosed [HasBinaryCoproducts C] [MonoidalClosed C] (X Y Z : C) :
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

instance distributive_of_closed [HasBinaryCoproducts C] [MonoidalClosed C] :
    MonoidalLeftDistributive C where
  is_iso_distributorLeft {X Y Z} := Iso.isIso_hom (isoDistributorOfClosed X Y Z)

attribute [local instance] endofunctorMonoidalCategory

instance endofunctors :
    MonoidalLeftDistributive (C ⥤ C) where
  is_iso_distributorLeft := by
    intro X Y Z
    refine ⟨?_, ?_, ?_⟩
    · exact {
    app (c : C) :=
    coprodObjIso Y Z (X.obj c) ≪≫ (coprodObjIso (X ⊗ Y) (X ⊗ Z) c).symm |>.hom
    }
    · ext c <;> simp [coprodObjIso]
    · ext c
      simp only [coprodObjIso, distributorLeft]
      aesop

end MonoidalDistributive

end CategoryTheory
