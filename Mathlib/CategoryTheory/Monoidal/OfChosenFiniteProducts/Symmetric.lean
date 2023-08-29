/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic

#align_import category_theory.monoidal.of_chosen_finite_products.symmetric from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# The symmetric monoidal structure on a category with chosen finite products.

-/


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

variable (𝒯 : LimitCone (Functor.empty.{v} C))

variable (ℬ : ∀ X Y : C, LimitCone (pair X Y))

open MonoidalOfChosenFiniteProducts

namespace MonoidalOfChosenFiniteProducts

open MonoidalCategory

theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensorHom ℬ f g ≫ (Limits.BinaryFan.braiding (ℬ Y Y').isLimit (ℬ Y' Y).isLimit).hom =
      (Limits.BinaryFan.braiding (ℬ X X').isLimit (ℬ X' X).isLimit).hom ≫ tensorHom ℬ g f := by
  dsimp [tensorHom, Limits.BinaryFan.braiding]
  -- ⊢ IsLimit.lift (ℬ Y Y').isLimit (BinaryFan.mk (BinaryFan.fst (ℬ X X').cone ≫ f …
  apply (ℬ _ _).isLimit.hom_ext
  -- ⊢ ∀ (j : Discrete WalkingPair), (IsLimit.lift (ℬ Y Y').isLimit (BinaryFan.mk ( …
  rintro ⟨⟨⟩⟩ <;> · dsimp [Limits.IsLimit.conePointUniqueUpToIso]; simp
  -- ⊢ (IsLimit.lift (ℬ Y Y').isLimit (BinaryFan.mk (BinaryFan.fst (ℬ X X').cone ≫  …
                    -- ⊢ (IsLimit.lift (ℬ Y Y').isLimit (BinaryFan.mk (BinaryFan.fst (ℬ X X').cone ≫  …
                                                                   -- 🎉 no goals
                    -- ⊢ (IsLimit.lift (ℬ Y Y').isLimit (BinaryFan.mk (BinaryFan.fst (ℬ X X').cone ≫  …
                                                                   -- 🎉 no goals
#align category_theory.monoidal_of_chosen_finite_products.braiding_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.braiding_naturality

theorem hexagon_forward (X Y Z : C) :
    (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫
        (Limits.BinaryFan.braiding (ℬ X (tensorObj ℬ Y Z)).isLimit
              (ℬ (tensorObj ℬ Y Z) X).isLimit).hom ≫
          (BinaryFan.associatorOfLimitCone ℬ Y Z X).hom =
      tensorHom ℬ (Limits.BinaryFan.braiding (ℬ X Y).isLimit (ℬ Y X).isLimit).hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ Y X Z).hom ≫
          tensorHom ℬ (𝟙 Y) (Limits.BinaryFan.braiding (ℬ X Z).isLimit (ℬ Z X).isLimit).hom := by
  dsimp [tensorHom, Limits.BinaryFan.braiding]
  -- ⊢ (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ (IsLimit.conePointUniqueUpTo …
  apply (ℬ _ _).isLimit.hom_ext; rintro ⟨⟨⟩⟩
  -- ⊢ ∀ (j : Discrete WalkingPair), ((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom …
                                 -- ⊢ ((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ (IsLimit.conePointUniqueUpT …
  · dsimp [Limits.IsLimit.conePointUniqueUpToIso]; simp
    -- ⊢ ((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ IsLimit.lift (ℬ (tensorObj  …
                                                   -- 🎉 no goals
  · apply (ℬ _ _).isLimit.hom_ext
    -- ⊢ ∀ (j : Discrete WalkingPair), (((BinaryFan.associatorOfLimitCone ℬ X Y Z).ho …
    rintro ⟨⟨⟩⟩ <;> · dsimp [Limits.IsLimit.conePointUniqueUpToIso]; simp
    -- ⊢ (((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ (IsLimit.conePointUniqueUp …
                      -- ⊢ (((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ IsLimit.lift (ℬ (tensorObj …
                                                                     -- 🎉 no goals
                      -- ⊢ (((BinaryFan.associatorOfLimitCone ℬ X Y Z).hom ≫ IsLimit.lift (ℬ (tensorObj …
                                                                     -- 🎉 no goals
#align category_theory.monoidal_of_chosen_finite_products.hexagon_forward CategoryTheory.MonoidalOfChosenFiniteProducts.hexagon_forward

theorem hexagon_reverse (X Y Z : C) :
    (BinaryFan.associatorOfLimitCone ℬ X Y Z).inv ≫
        (Limits.BinaryFan.braiding (ℬ (tensorObj ℬ X Y) Z).isLimit
              (ℬ Z (tensorObj ℬ X Y)).isLimit).hom ≫
          (BinaryFan.associatorOfLimitCone ℬ Z X Y).inv =
      tensorHom ℬ (𝟙 X) (Limits.BinaryFan.braiding (ℬ Y Z).isLimit (ℬ Z Y).isLimit).hom ≫
        (BinaryFan.associatorOfLimitCone ℬ X Z Y).inv ≫
          tensorHom ℬ (Limits.BinaryFan.braiding (ℬ X Z).isLimit (ℬ Z X).isLimit).hom (𝟙 Y) := by
  dsimp [tensorHom, Limits.BinaryFan.braiding]
  -- ⊢ (BinaryFan.associatorOfLimitCone ℬ X Y Z).inv ≫ (IsLimit.conePointUniqueUpTo …
  apply (ℬ _ _).isLimit.hom_ext; rintro ⟨⟨⟩⟩
  -- ⊢ ∀ (j : Discrete WalkingPair), ((BinaryFan.associatorOfLimitCone ℬ X Y Z).inv …
                                 -- ⊢ ((BinaryFan.associatorOfLimitCone ℬ X Y Z).inv ≫ (IsLimit.conePointUniqueUpT …
  · apply (ℬ _ _).isLimit.hom_ext
    -- ⊢ ∀ (j : Discrete WalkingPair), (((BinaryFan.associatorOfLimitCone ℬ X Y Z).in …
    rintro ⟨⟨⟩⟩ <;>
    -- ⊢ (((BinaryFan.associatorOfLimitCone ℬ X Y Z).inv ≫ (IsLimit.conePointUniqueUp …
      · dsimp [BinaryFan.associatorOfLimitCone, BinaryFan.associator,
          Limits.IsLimit.conePointUniqueUpToIso]
        simp
        -- 🎉 no goals
        -- 🎉 no goals
  · dsimp [BinaryFan.associatorOfLimitCone, BinaryFan.associator,
      Limits.IsLimit.conePointUniqueUpToIso]
    simp
    -- 🎉 no goals
#align category_theory.monoidal_of_chosen_finite_products.hexagon_reverse CategoryTheory.MonoidalOfChosenFiniteProducts.hexagon_reverse

theorem symmetry (X Y : C) :
    (Limits.BinaryFan.braiding (ℬ X Y).isLimit (ℬ Y X).isLimit).hom ≫
        (Limits.BinaryFan.braiding (ℬ Y X).isLimit (ℬ X Y).isLimit).hom =
      𝟙 (tensorObj ℬ X Y) := by
  dsimp [tensorHom, Limits.BinaryFan.braiding]
  -- ⊢ (IsLimit.conePointUniqueUpToIso (ℬ X Y).isLimit (IsLimit.swapBinaryFan (ℬ Y  …
  apply (ℬ _ _).isLimit.hom_ext;
  -- ⊢ ∀ (j : Discrete WalkingPair), ((IsLimit.conePointUniqueUpToIso (ℬ X Y).isLim …
  rintro ⟨⟨⟩⟩ <;> · dsimp [Limits.IsLimit.conePointUniqueUpToIso]; simp
  -- ⊢ ((IsLimit.conePointUniqueUpToIso (ℬ X Y).isLimit (IsLimit.swapBinaryFan (ℬ Y …
                    -- ⊢ (IsLimit.lift (ℬ Y X).isLimit (BinaryFan.swap (ℬ X Y).cone) ≫ IsLimit.lift ( …
                                                                   -- 🎉 no goals
                    -- ⊢ (IsLimit.lift (ℬ Y X).isLimit (BinaryFan.swap (ℬ X Y).cone) ≫ IsLimit.lift ( …
                                                                   -- 🎉 no goals
#align category_theory.monoidal_of_chosen_finite_products.symmetry CategoryTheory.MonoidalOfChosenFiniteProducts.symmetry

end MonoidalOfChosenFiniteProducts

open MonoidalOfChosenFiniteProducts

/-- The monoidal structure coming from finite products is symmetric.
-/
def symmetricOfChosenFiniteProducts : SymmetricCategory (MonoidalOfChosenFiniteProductsSynonym 𝒯 ℬ)
    where
  braiding _ _ := Limits.BinaryFan.braiding (ℬ _ _).isLimit (ℬ _ _).isLimit
  braiding_naturality f g := braiding_naturality ℬ f g
  hexagon_forward X Y Z := hexagon_forward ℬ X Y Z
  hexagon_reverse X Y Z := hexagon_reverse ℬ X Y Z
  symmetry X Y := symmetry ℬ X Y
#align category_theory.symmetric_of_chosen_finite_products CategoryTheory.symmetricOfChosenFiniteProducts

end CategoryTheory
