/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# AB axioms in the category of ind-objects

We show that `Ind C` satisfies Grothendieck's axiom AB5 if `C` has finite limits.
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

instance {J : Type v} [SmallCategory J] [IsFiltered J] [HasFiniteLimits C] :
    HasExactColimitsOfShape J (Ind C) :=
  HasExactColimitsOfShape.domain_of_functor J (Ind.inclusion C)

instance [HasFiniteLimits C] : AB5 (Ind C) where
  ofShape _ _ _ := inferInstance

end CategoryTheory.Limits
