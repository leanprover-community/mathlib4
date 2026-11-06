/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂

namespace CategoryTheory.Subfunctor

open Limits

-- refactor `SimplicialSet/SubcomplexEvaluation.lean`
instance {C : Type*} [Category* C] {J : Type*} [Category* J]
    {F : C ⥤ Type w} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subfunctor.toFunctorFunctor (F := F)) where
  preservesColimit := sorry

end CategoryTheory.Subfunctor
