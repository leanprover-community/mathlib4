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

namespace Mon_Class

theorem lift_lift_assoc {A : C} {B : C} [Mon_Class B] (f g h : A ⟶ B) :
    lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ := by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_left {A : C} {B : C} [Mon_Class B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
    lift (f ≫ η) g ≫ μ = g := by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_right {A : C} {B : C} [Mon_Class B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ η) ≫ μ = f := by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

end Mon_Class
