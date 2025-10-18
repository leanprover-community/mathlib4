/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Linear monoidal categories

A monoidal category is `MonoidalLinear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type*) [Semiring R]
variable (C : Type*) [Category C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C]

/-- A category is `MonoidalLinear R` if tensoring is `R`-linear in both factors.
-/
class MonoidalLinear [MonoidalPreadditive C] : Prop where
  whiskerLeft_smul : ∀ (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f) := by
    cat_disch
  smul_whiskerRight : ∀ (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X) := by
    cat_disch

attribute [simp] MonoidalLinear.whiskerLeft_smul MonoidalLinear.smul_whiskerRight

variable {C}
variable [MonoidalPreadditive C] [MonoidalLinear R C]

instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where

instance tensorRight_linear (X : C) : (tensorRight X).Linear R where

instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where

instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where

/-- A faithful linear monoidal functor to a linear monoidal category
ensures that the domain is linear monoidal. -/
theorem monoidalLinearOfFaithful {D : Type*} [Category D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : D ⥤ C) [F.Monoidal] [F.Faithful]
    [F.Linear R] : MonoidalLinear R D :=
  { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }

end CategoryTheory
