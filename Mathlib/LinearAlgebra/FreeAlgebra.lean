/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.SetTheory.Cardinal.Free

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

namespace Algebra

open Cardinal

variable (R : Type u) {S : Type v} (s : Set S)

theorem rank_adjoin_le [CommRing R] [Ring S] [Algebra R S] :
    Module.rank R (adjoin R s) ≤ max #s ℵ₀ := by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s → S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq, lift_id'.{v,u}, lift_umax.{v,u}, lift_le, max_comm]
  exact mk_list_le_max _

theorem lift_cardinalMk_adjoin_le [CommSemiring R] [Semiring S] [Algebra R S] :
    lift.{u} #(adjoin R s) ≤ max (max (lift.{v} #R) (lift.{u} #s)) ℵ₀ := by
  by_cases hs : s = ∅
  · simp_rw [hs, adjoin_empty, mk_eq_zero, lift_zero]
    simp only [zero_le, sup_of_le_left]
    exact (lift_mk_le_lift_mk_of_surjective (f := algebraMap R (⊥ : Subalgebra R S)) <| by
      rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩).trans le_sup_left
  rcases subsingleton_or_nontrivial R with _ | _
  · haveI := (algebraMap R (adjoin R s)).codomain_trivial
    exact (lift_le_aleph0.2 mk_le_aleph0).trans le_sup_right
  rw [← Ne, ← Set.nonempty_iff_ne_empty'] at hs
  rw [adjoin_eq_range_freeAlgebra_lift]
  have hs' := mk_freeMonoid s
  haveI : Infinite (FreeMonoid s) := infinite_iff.2 (by simp [hs'])
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s → S))
  rwa [lift_umax, lift_id'.{v, u}, FreeAlgebra.equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra, mk_finsupp_lift_of_infinite, hs', lift_max, lift_aleph0, sup_comm,
    ← sup_assoc] at H

end Algebra
