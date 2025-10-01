/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Abelian.Indization
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Generator.Indization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

@[expose] public section

/-!
# AB axioms in the category of ind-objects

We show that `Ind C` satisfies Grothendieck's axiom AB5 if `C` has finite limits and deduce that
`Ind C` is Grothendieck abelian if `C` is small and abelian.
-/

universe v u

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C]

instance {J : Type v} [SmallCategory J] [IsFiltered J] [HasFiniteLimits C] :
    HasExactColimitsOfShape J (Ind C) :=
  HasExactColimitsOfShape.domain_of_functor J (Ind.inclusion C)

instance [HasFiniteLimits C] : AB5 (Ind C) where
  ofShape _ _ _ := inferInstance

end

section

variable {C : Type u} [SmallCategory C] [Abelian C]

instance isGrothendieckAbelian_ind : IsGrothendieckAbelian.{u} (Ind C) where
  hasSeparator := ⟨⟨_, Ind.isSeparator_range_yoneda⟩⟩

end

end CategoryTheory.Limits
