/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Distributive monoidal categories

## Main definitions

A monoidal category `C` with binary coproducts is left distributive if the left tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` can be promoted to an isomorphism. We refer to
this isomorphism as the left distributivity isomorphism.

A monoidal category `C` with binary coproducts is right distributive if the right tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X` can be promoted to an isomorphism. We refer to
this isomorphism as the right distributivity isomorphism.

A distributive monoidal category is a monoidal category that is both left and right distributive.

## Main results

- A symmetric monoidal category is left distributive if and only if it is right distributive.

- A closed monoidal category is left distributive.

- For a category `C` the category of endofunctors `C ⥤ C` is left distributive (but almost
  never right distributive). The left distributivity is tantamount to the fact that the coproduct
  in the functor categories is computed pointwise.

- We show that any preadditive monoidal category with coproducts is distributive. This includes the
examples of abelian groups, R-modules, and vector bundles.

## TODO

Show that a distributive monoidal category whose unit is weakly terminal is finitary distributive.

Show that the category of pointed types with the monoidal structure given by the smash product of
pointed types and the coproduct given by the wedge sum is distributive.

## References

* [Hans-Joachim Baues, Mamuka Jibladze, Andy Tonks, Cohomology of
  monoids in monoidal categories, in: Operads: Proceedings of Renaissance
  Conferences, Contemporary Mathematics 202, AMS (1997) 137-166][MR1268290]

-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits Iso

/-- A monoidal category with binary coproducts is left distributive
if the left tensor product functor preserves binary coproducts. -/
class IsMonoidalLeftDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorLeft (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) := by infer_instance

/-- A monoidal category with binary coproducts is right distributive
if the right tensor product functor preserves binary coproducts. -/
class IsMonoidalRightDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorRight (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X) := by infer_instance

/-- A monoidal category with binary coproducts is distributive
if it is both left and right distributive. -/
class IsMonoidalDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] extends
  IsMonoidalLeftDistrib C, IsMonoidalRightDistrib C

variable {C} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

section IsMonoidalLeftDistrib

attribute [instance] IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft

/-- The canonical left distributivity isomorphism -/
def leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  PreservesColimitPair.iso (tensorLeft X) Y Z

end IsMonoidalLeftDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical left distributivity isomorphism -/
scoped notation "∂L" => leftDistrib

end Distributive

open Distributive

lemma IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorLeft X) Y Z)] : IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X :=
    preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)

/-- The forward direction of the left distributivity isomorphism is the cogap morphism
`coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)`. -/
lemma leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) := by rfl

@[reassoc (attr := simp)]
lemma coprod_inl_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂L X Y Z).hom = X ◁ coprod.inl := by
  rw [leftDistrib_hom, coprod.inl_desc]

@[reassoc (attr := simp)]
lemma coprod_inr_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂L X Y Z).hom = X ◁ coprod.inr := by
  rw [leftDistrib_hom, coprod.inr_desc]

/-- The composite of `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_coprod_inl_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inl) ≫ (∂L X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_leftDistrib_hom]

/-- The composite of `(X ◁ coprod.inr) : X ⊗ Z ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the right coprojection `coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_coprod_inr_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inr) ≫ (∂L X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_leftDistrib_hom]

section IsMonoidalRightDistrib

attribute [instance] IsMonoidalRightDistrib.preservesBinaryCoproducts_tensorRight

/-- The canonical right distributivity isomorphism -/
def rightDistrib [IsMonoidalRightDistrib C] (X Y Z : C) : (Y ⊗ X) ⨿ (Z ⊗ X) ≅ (Y ⨿ Z) ⊗ X :=
  PreservesColimitPair.iso (tensorRight X) Y Z

end IsMonoidalRightDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical right distributivity isomorphism -/
notation "∂R" => rightDistrib

end Distributive

lemma IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorRight X) Y Z)] :
    IsMonoidalRightDistrib C where
  preservesBinaryCoproducts_tensorRight _ :=
    ⟨preservesBinaryCoproducts_of_isIso_coprodComparison _ |>.preservesColimit⟩

/-- The forward direction of the right distributivity isomorphism is equal to the cogap morphism
`coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X`. -/
lemma rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) := by rfl

@[reassoc (attr := simp)]
lemma coprod_inl_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂R X Y Z).hom = coprod.inl ▷ X := by
  rw [rightDistrib_hom, coprod.inl_desc]

@[reassoc (attr := simp)]
lemma coprod_inr_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂R X Y Z).hom = coprod.inr ▷ X := by
  rw [rightDistrib_hom, coprod.inr_desc]

/-- The composite of `(coprod.inl ▷ X) : Y ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the left coprojection
`coprod.inl : Y ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_coprod_inl_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inl ▷ X) ≫ (∂R X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_rightDistrib_hom]

/-- The composite of `(coprod.inr ▷ X) : Z ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the right coprojection
`coprod.inr : Z ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_coprod_inr_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inr ▷ X) ≫ (∂R X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_rightDistrib_hom]

/-- In a symmetric monoidal category, the left distributivity is equal to
the right distributivity up to braiding isomorphisms. -/
@[simp]
lemma coprodComparison_tensorLeft_braiding_hom [BraidedCategory C] {X Y Z : C} :
    (coprodComparison (tensorLeft X) Y Z) ≫ (β_ X (Y ⨿ Z)).hom =
    (coprod.map (β_ X Y).hom (β_ X Z).hom) ≫ (coprodComparison (tensorRight X) Y Z) := by
  simp [coprodComparison]

/-- In a symmetric monoidal category, the right distributivity is equal to
the left distributivity up to braiding isomorphisms. -/
@[simp]
lemma coprodComparison_tensorRight_braiding_hom [SymmetricCategory C] {X Y Z : C} :
    (coprodComparison (tensorRight X) Y Z) ≫ (β_ (Y ⨿ Z) X).hom =
    (coprod.map (β_ Y X).hom (β_ Z X).hom) ≫ (coprodComparison (tensorLeft X) Y Z) := by
  simp [coprodComparison]

/-- A left distributive symmetric monoidal category is distributive. -/
lemma SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] : IsMonoidalDistrib C where
      preservesBinaryCoproducts_tensorRight X :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The right distributivity isomorphism of the a left distributive symmetric monoidal category
is given by `(β_ (Y ⨿ Z) X).hom ≫ (∂L X Y Z).inv ≫ (coprod.map (β_ X Y).hom (β_ X Z).hom)`. -/
@[simp]
lemma SymmetricCategory.rightDistrib_of_leftDistrib
    [SymmetricCategory C] [IsMonoidalDistrib C] {X Y Z : C} :
    ∂R X Y Z = (coprod.mapIso (β_ Y X) (β_ Z X)) ≪≫ (∂L X Y Z) ≪≫ (β_ X (Y ⨿ Z)) := by
  ext <;> simp [leftDistrib_hom, rightDistrib_hom]

/-- A closed monoidal category is left distributive. -/
instance MonoidalClosed.isMonoidalLeftDistrib [MonoidalClosed C] :
    IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X := by
    infer_instance

instance isMonoidalDistrib.of_symmetric_monoidal_closed [SymmetricCategory C] [MonoidalClosed C] :
    IsMonoidalDistrib C := by
  apply SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

/-- The inverse of distributivity isomorphism from the closed monoidal structure -/
lemma MonoidalClosed.leftDistrib_inv [MonoidalClosed C] {X Y Z : C} :
    (leftDistrib X Y Z).inv =
      uncurry (coprod.desc (curry coprod.inl) (curry coprod.inr)) := by
  rw [← curry_eq_iff]
  ext <;> simp [← curry_natural_left]

section Endofunctors

attribute [local instance] endofunctorMonoidalCategory

/-- The monoidal structure on the category of endofunctors is left distributive. -/
instance isMonoidalLeftDistrib.of_endofunctors : IsMonoidalLeftDistrib (C ⥤ C) where
  preservesBinaryCoproducts_tensorLeft F :=
    inferInstanceAs (PreservesColimitsOfShape _ ((Functor.whiskeringLeft C C C).obj F))

end Endofunctors

section MonoidalPreadditive

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
  preservesBinaryCoproducts_of_preservesBinaryBiproducts

/-- A preadditive monoidal category with binary biproducts is distributive. -/
instance IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts [Preadditive C]
    [MonoidalPreadditive C] :
    IsMonoidalDistrib C where

end MonoidalPreadditive

end CategoryTheory
