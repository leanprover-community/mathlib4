/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
/-!

# AB axioms in sheaf categories

This file proves that, when the relevant limits and colimits and sheafification exist, exactness of
limits and colimits carries over from `A` to categories of `A`-valued sheaves.
-/

namespace CategoryTheory

open Limits

variable {A C J : Type*} [Category A] [Category C] [Category J]

variable (K : GrothendieckTopology C) [HasWeakSheafify K A]

instance [HasFiniteLimits A] [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [PreservesColimitsOfShape J (sheafToPresheaf K A)] : HasExactColimitsOfShape J (Sheaf K A) :=
  HasExactColimitsOfShape.domain_of_functor J (sheafToPresheaf K A)

instance [HasFiniteColimits A] [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [PreservesFiniteColimits (sheafToPresheaf K A)] : HasExactLimitsOfShape J (Sheaf K A) :=
  HasExactLimitsOfShape.domain_of_functor J (sheafToPresheaf K A)

end CategoryTheory
