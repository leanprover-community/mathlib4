
/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.EqToHom

#align_import category_theory.bicategory.locally_discrete from "leanprover-community/mathlib"@"c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e"

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `LocallyDiscrete C`. The objects and the
1-morphisms in `LocallyDiscrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `LocallyDiscrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `LocallyDiscrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

namespace CategoryTheory

open Bicategory Discrete

open Bicategory


universe w₂ v v₁ v₂ u u₁ u₂

variable {C : Type u}

/-- A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext]
structure LocallyDiscrete (C : Type u) where
  as : C

namespace LocallyDiscrete

@[simp]
theorem mk_as (a : LocallyDiscrete C) : LocallyDiscrete.mk a.as = a := rfl

@[simps]
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

instance [Inhabited C] : Inhabited (LocallyDiscrete C) := ⟨⟨default⟩⟩

instance [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C)
    where
  Hom := fun X Y => Discrete (X.as ⟶ Y.as)
  id := fun X => ⟨𝟙 X.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

instance (priority := 900) homSmallCategory (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  CategoryTheory.discreteCategory (X.as ⟶ Y.as)
#align category_theory.locally_discrete.hom_small_category CategoryTheory.LocallyDiscrete.homSmallCategory

-- Porting note: Manually adding this instance (inferInstance doesn't work)
instance subsingleton2Hom {X Y : LocallyDiscrete C} (f g : X ⟶ Y) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext _ _ η.1.1
#align category_theory.locally_discrete.eq_of_hom CategoryTheory.LocallyDiscrete.eq_of_hom

end LocallyDiscrete
