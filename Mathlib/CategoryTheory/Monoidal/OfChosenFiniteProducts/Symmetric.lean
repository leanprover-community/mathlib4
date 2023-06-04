/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon

! This file was ported from Lean 3 source module category_theory.monoidal.of_chosen_finite_products.symmetric
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic

/-!
# The symmetric monoidal structure on a category with chosen finite products.

-/


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

attribute [local tidy] tactic.case_bash

variable {C}

variable (𝒯 : LimitCone (Functor.empty.{v} C))

variable (ℬ : ∀ X Y : C, LimitCone (pair X Y))

open MonoidalOfChosenFiniteProducts

namespace MonoidalOfChosenFiniteProducts

open MonoidalCategory

theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensorHom ℬ f g ≫ (Limits.BinaryFan.braiding (ℬ Y Y').IsLimit (ℬ Y' Y).IsLimit).Hom =
      (Limits.BinaryFan.braiding (ℬ X X').IsLimit (ℬ X' X).IsLimit).Hom ≫ tensorHom ℬ g f :=
  by
  dsimp [tensor_hom, limits.binary_fan.braiding]
  apply (ℬ _ _).IsLimit.hom_ext;
  rintro ⟨⟨⟩⟩ <;> · dsimp [limits.is_limit.cone_point_unique_up_to_iso]; simp
#align category_theory.monoidal_of_chosen_finite_products.braiding_naturality CategoryTheory.monoidalOfChosenFiniteProducts.braiding_naturality

theorem hexagon_forward (X Y Z : C) :
    (BinaryFan.associatorOfLimitCone ℬ X Y Z).Hom ≫
        (Limits.BinaryFan.braiding (ℬ X (tensorObj ℬ Y Z)).IsLimit
              (ℬ (tensorObj ℬ Y Z) X).IsLimit).Hom ≫
          (BinaryFan.associatorOfLimitCone ℬ Y Z X).Hom =
      tensorHom ℬ (Limits.BinaryFan.braiding (ℬ X Y).IsLimit (ℬ Y X).IsLimit).Hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ Y X Z).Hom ≫
          tensorHom ℬ (𝟙 Y) (Limits.BinaryFan.braiding (ℬ X Z).IsLimit (ℬ Z X).IsLimit).Hom :=
  by
  dsimp [tensor_hom, limits.binary_fan.braiding]
  apply (ℬ _ _).IsLimit.hom_ext; rintro ⟨⟨⟩⟩
  · dsimp [limits.is_limit.cone_point_unique_up_to_iso]; simp
  · apply (ℬ _ _).IsLimit.hom_ext;
    rintro ⟨⟨⟩⟩ <;> · dsimp [limits.is_limit.cone_point_unique_up_to_iso]; simp
#align category_theory.monoidal_of_chosen_finite_products.hexagon_forward CategoryTheory.monoidalOfChosenFiniteProducts.hexagon_forward

theorem hexagon_reverse (X Y Z : C) :
    (BinaryFan.associatorOfLimitCone ℬ X Y Z).inv ≫
        (Limits.BinaryFan.braiding (ℬ (tensorObj ℬ X Y) Z).IsLimit
              (ℬ Z (tensorObj ℬ X Y)).IsLimit).Hom ≫
          (BinaryFan.associatorOfLimitCone ℬ Z X Y).inv =
      tensorHom ℬ (𝟙 X) (Limits.BinaryFan.braiding (ℬ Y Z).IsLimit (ℬ Z Y).IsLimit).Hom ≫
        (BinaryFan.associatorOfLimitCone ℬ X Z Y).inv ≫
          tensorHom ℬ (Limits.BinaryFan.braiding (ℬ X Z).IsLimit (ℬ Z X).IsLimit).Hom (𝟙 Y) :=
  by
  dsimp [tensor_hom, limits.binary_fan.braiding]
  apply (ℬ _ _).IsLimit.hom_ext; rintro ⟨⟨⟩⟩
  · apply (ℬ _ _).IsLimit.hom_ext;
    rintro ⟨⟨⟩⟩ <;>
      · dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
          limits.is_limit.cone_point_unique_up_to_iso]
        simp
  · dsimp [binary_fan.associator_of_limit_cone, binary_fan.associator,
      limits.is_limit.cone_point_unique_up_to_iso]
    simp
#align category_theory.monoidal_of_chosen_finite_products.hexagon_reverse CategoryTheory.monoidalOfChosenFiniteProducts.hexagon_reverse

theorem symmetry (X Y : C) :
    (Limits.BinaryFan.braiding (ℬ X Y).IsLimit (ℬ Y X).IsLimit).Hom ≫
        (Limits.BinaryFan.braiding (ℬ Y X).IsLimit (ℬ X Y).IsLimit).Hom =
      𝟙 (tensorObj ℬ X Y) :=
  by
  dsimp [tensor_hom, limits.binary_fan.braiding]
  apply (ℬ _ _).IsLimit.hom_ext;
  rintro ⟨⟨⟩⟩ <;> · dsimp [limits.is_limit.cone_point_unique_up_to_iso]; simp
#align category_theory.monoidal_of_chosen_finite_products.symmetry CategoryTheory.monoidalOfChosenFiniteProducts.symmetry

end MonoidalOfChosenFiniteProducts

open MonoidalOfChosenFiniteProducts

/-- The monoidal structure coming from finite products is symmetric.
-/
def symmetricOfChosenFiniteProducts : SymmetricCategory (MonoidalOfChosenFiniteProductsSynonym 𝒯 ℬ)
    where
  braiding X Y := Limits.BinaryFan.braiding (ℬ _ _).IsLimit (ℬ _ _).IsLimit
  braiding_naturality' X X' Y Y' f g := braiding_naturality ℬ f g
  hexagon_forward' X Y Z := hexagon_forward ℬ X Y Z
  hexagon_reverse' X Y Z := hexagon_reverse ℬ X Y Z
  symmetry' X Y := symmetry ℬ X Y
#align category_theory.symmetric_of_chosen_finite_products CategoryTheory.symmetricOfChosenFiniteProducts

end

end CategoryTheory

