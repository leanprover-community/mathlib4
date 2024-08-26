/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# If `D` has finite (co)limits, so do the functor categories `C ⥤ D`.

These are boiler-plate instances, in their own file as neither import otherwise needs the other.
-/


open CategoryTheory

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

instance functor_category_hasFiniteLimits [HasFiniteLimits D] : HasFiniteLimits (C ⥤ D) where
  out _ _ _ := inferInstance

instance functor_category_hasFiniteColimits [HasFiniteColimits D] : HasFiniteColimits (C ⥤ D) where
  out _ _ _ := inferInstance

end CategoryTheory.Limits
