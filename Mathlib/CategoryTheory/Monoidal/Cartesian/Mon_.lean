/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Additional results about monoid objects in cartesian monoidal categories
-/

universe v₁ u₁

open CategoryTheory MonoidalCategory ChosenFiniteProducts

variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts.{v₁} C]

namespace Mon_

theorem lift_lift_assoc {A : C} {B : Mon_ C} (f g h : A ⟶ B.X) :
    lift (lift f g ≫ B.mul) h ≫ B.mul = lift f (lift g h ≫ B.mul) ≫ B.mul := by
  have := lift (lift f g) h ≫= B.mul_assoc
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_left {A : C} {B : Mon_ C} (f : A ⟶ 𝟙_ C) (g : A ⟶ B.X) :
    lift (f ≫ B.one) g ≫ B.mul = g := by
  have := lift f g ≫= B.one_mul
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_right {A : C} {B : Mon_ C} (f : A ⟶ B.X) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ B.one) ≫ B.mul = f := by
  have := lift f g ≫= B.mul_one
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

end Mon_
