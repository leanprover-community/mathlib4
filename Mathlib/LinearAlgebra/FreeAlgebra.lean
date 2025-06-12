/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Subsingleton
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Linear algebra properties of `FreeAlgebra R X`

This file provides a `FreeMonoid X` basis on the `FreeAlgebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `List X`
-/


universe u v

namespace FreeAlgebra

variable (R : Type u) (X : Type v)

section
variable [CommSemiring R]

/-- The `FreeMonoid X` basis on the `FreeAlgebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
-- @[simps]
noncomputable def basisFreeMonoid : Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map (equivMonoidAlgebraFreeMonoid (R := R) (X := X)).symm.toLinearEquiv

instance : Module.Free R (FreeAlgebra R X) :=
  have : Module.Free R (MonoidAlgebra R (FreeMonoid X)) := Module.Free.finsupp _ _ _
  Module.Free.of_equiv (equivMonoidAlgebraFreeMonoid (R := R) (X := X)).symm.toLinearEquiv

end

theorem rank_eq [CommRing R] [Nontrivial R] :
    Module.rank R (FreeAlgebra R X) = Cardinal.lift.{u} (Cardinal.mk (List X)) := by
  rw [← (Basis.mk_eq_rank'.{_,_,_,u} (basisFreeMonoid R X)).trans (Cardinal.lift_id _),
    Cardinal.lift_umax.{v, u}, FreeMonoid]

end FreeAlgebra

open Cardinal

theorem Algebra.rank_adjoin_le {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
    (s : Set S) : Module.rank R (adjoin R s) ≤ max #s ℵ₀ := by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s → S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq, lift_id'.{v,u}, lift_umax.{v,u}, lift_le, max_comm]
  exact mk_list_le_max _
