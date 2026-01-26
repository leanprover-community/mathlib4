import Mathlib.CategoryTheory.Idempotents.Basic

/-!

# Idempotent completeness of categories of simplicial objects

In this file, we provide an instance expressing that `SimplicialObject C`
and `CosimplicialObject C` are idempotent complete categories when the
category `C` is.

-/

@[expose] public section


namespace CategoryTheory

namespace Idempotents

variable {C : Type*} [Category* C] [IsIdempotentComplete C]

instance : IsIdempotentComplete (SimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

instance : IsIdempotentComplete (CosimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

end Idempotents

end CategoryTheory
