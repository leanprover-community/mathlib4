/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.FinsuppVectorSpace

#align_import linear_algebra.free_algebra from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# Linear algebra properties of `FreeAlgebra R X`

This file provides a `FreeMonoid X` basis on the `FreeAlgebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `List X`
-/


universe u v

namespace FreeAlgebra

/-- The `FreeMonoid X` basis on the `FreeAlgebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
-- @[simps]
noncomputable def basisFreeMonoid (R : Type u) (X : Type v) [CommRing R] :
    Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map (equivMonoidAlgebraFreeMonoid (R := R) (X := X)).symm.toLinearEquiv
#align free_algebra.basis_free_monoid FreeAlgebra.basisFreeMonoid

-- TODO: generalize to `X : Type v`
theorem rank_eq {K : Type u} {X : Type max u v} [Field K] :
    Module.rank K (FreeAlgebra K X) = Cardinal.mk (List X) :=
  -- Porting note: the type class inference was no longer automatic.
  -- was: (Cardinal.lift_inj.mp (basisFreeMonoid K X).mk_eq_rank).symm
  Cardinal.lift_inj.mp (@Basis.mk_eq_rank _ _ _ _ _ _ (inferInstance : Module K (FreeAlgebra K X))
  (basisFreeMonoid K X)).symm
#align free_algebra.rank_eq FreeAlgebra.rank_eq

end FreeAlgebra
