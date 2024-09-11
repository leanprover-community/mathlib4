/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Preadditive

/-!
# Linear semigroupal categories

A semigroupal category is `SemigroupalLinear R` if it is semigroupal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.SemigroupalCategory

variable (R : Type*) [Semiring R]
variable (C : Type*) [Category C] [Preadditive C] [Linear R C]
variable [SemigroupalCategory C]

-- Porting note: added `SemigroupalPreadditive` as argument ``
/-- A category is `SemigroupalLinear R` if tensoring is `R`-linear in both factors.
-/
class SemigroupalLinear [SemigroupalPreadditive C] : Prop where
  whiskerLeft_smul : ∀ (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z) , X ◁ (r • f) = r • (X ◁ f) := by
    aesop_cat
  smul_whiskerRight : ∀ (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X) := by
    aesop_cat

attribute [simp] SemigroupalLinear.whiskerLeft_smul SemigroupalLinear.smul_whiskerRight

variable {C}
variable [SemigroupalPreadditive C] [SemigroupalLinear R C]

instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where

instance tensorRight_linear (X : C) : (tensorRight X).Linear R where

instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where

instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where

/-- A faithful linear semigroupal functor to a linear semigroupal category
ensures that the domain is linear semigroupal. -/
theorem semigroupalLinearOfFaithful {D : Type*} [Category D] [Preadditive D] [Linear R D]
    [SemigroupalCategory D] [SemigroupalPreadditive D] (F : SemigroupalFunctor D C) [F.Faithful]
    [F.toFunctor.Additive] [F.toFunctor.Linear R] : SemigroupalLinear R D :=
  { whiskerLeft_smul := by
      intros X Y Z r f
      apply F.toFunctor.map_injective
      rw [F.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intros r X Y f Z
      apply F.toFunctor.map_injective
      rw [F.map_whiskerRight]
      simp }

end CategoryTheory
