/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive

#align_import category_theory.monoidal.linear from "leanprover-community/mathlib"@"986c4d5761f938b2e1c43c01f001b6d9d88c2055"

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

-- porting note: added `MonoidalPreadditive` as argument ``
/-- A category is `MonoidalLinear R` if tensoring is `R`-linear in both factors.
-/
class MonoidalLinear [MonoidalPreadditive C] : Prop where
  tensor_smul : ∀ {W X Y Z : C} (f : W ⟶ X) (r : R) (g : Y ⟶ Z), f ⊗ r • g = r • (f ⊗ g) := by
    aesop_cat
  smul_tensor : ∀ {W X Y Z : C} (r : R) (f : W ⟶ X) (g : Y ⟶ Z), r • f ⊗ g = r • (f ⊗ g) := by
    aesop_cat
#align category_theory.monoidal_linear CategoryTheory.MonoidalLinear

attribute [simp] MonoidalLinear.tensor_smul MonoidalLinear.smul_tensor

variable {C}
variable [MonoidalPreadditive C] [MonoidalLinear R C]

instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where
#align category_theory.tensor_left_linear CategoryTheory.tensorLeft_linear

instance tensorRight_linear (X : C) : (tensorRight X).Linear R where
#align category_theory.tensor_right_linear CategoryTheory.tensorRight_linear

instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where
#align category_theory.tensoring_left_linear CategoryTheory.tensoringLeft_linear

instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where
#align category_theory.tensoring_right_linear CategoryTheory.tensoringRight_linear

/-- A faithful linear monoidal functor to a linear monoidal category
ensures that the domain is linear monoidal. -/
theorem monoidalLinearOfFaithful {D : Type*} [Category D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : MonoidalFunctor D C) [Faithful F.toFunctor]
    [F.toFunctor.Additive] [F.toFunctor.Linear R] : MonoidalLinear R D :=
  { tensor_smul := by
      intros W X Y Z f r g
      apply F.toFunctor.map_injective
      simp only [F.toFunctor.map_smul r (f ⊗ g), F.toFunctor.map_smul r g, F.map_tensor,
        MonoidalLinear.tensor_smul, Linear.smul_comp, Linear.comp_smul]
    smul_tensor := by
      intros W X Y Z r f g
      apply F.toFunctor.map_injective
      simp only [F.toFunctor.map_smul r (f ⊗ g), F.toFunctor.map_smul r f, F.map_tensor,
        MonoidalLinear.smul_tensor, Linear.smul_comp, Linear.comp_smul] }
#align category_theory.monoidal_linear_of_faithful CategoryTheory.monoidalLinearOfFaithful

end CategoryTheory
