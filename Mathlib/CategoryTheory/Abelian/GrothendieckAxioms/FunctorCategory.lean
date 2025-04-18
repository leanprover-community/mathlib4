/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-!

# AB axioms in functor categories

This file proves that, when the relevant limits and colimits exist, exactness of limits and
colimits carries over from `A` to the functor category `C ⥤ A`
-/

namespace CategoryTheory

open CategoryTheory Limits Opposite

variable {A C J : Type*} [Category A] [Category C] [Category J]

instance [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] [HasFiniteLimits A] :
    HasExactColimitsOfShape J (C ⥤ A) where
  preservesFiniteLimits := { preservesFiniteLimits _ := inferInstance }

instance [HasLimitsOfShape J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A] :
    HasExactLimitsOfShape J (C ⥤ A) where
  preservesFiniteColimits := { preservesFiniteColimits _ := inferInstance }

end CategoryTheory
