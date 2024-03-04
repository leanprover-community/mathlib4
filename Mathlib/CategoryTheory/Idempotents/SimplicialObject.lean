/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Idempotents.FunctorCategories

#align_import category_theory.idempotents.simplicial_object from "leanprover-community/mathlib"@"163d1a6d98caf9f0431704169027e49c5c6c6cc0"

/-!

# Idempotent completeness of categories of simplicial objects

In this file, we provide an instance expressing that `SimplicialObject C`
and `CosimplicialObject C` are idempotent complete categories when the
category `C` is.

-/


namespace CategoryTheory

namespace Idempotents

variable {C : Type*} [Category C] [IsIdempotentComplete C]

instance : IsIdempotentComplete (SimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

instance : IsIdempotentComplete (CosimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

end Idempotents

end CategoryTheory
