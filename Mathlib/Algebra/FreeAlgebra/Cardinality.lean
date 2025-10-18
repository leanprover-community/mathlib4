/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.SetTheory.Cardinal.Free

/-!
# Cardinality of free algebras

This file contains some results about the cardinality of `FreeAlgebra`,
parallel to that of `MvPolynomial`.
-/

universe u v

variable (R : Type u) [CommSemiring R]

open Cardinal

namespace FreeAlgebra

variable (X : Type v)

@[simp]
theorem cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] :
    #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra,
    mk_finsupp_lift_of_infinite, hX, lift_max, lift_aleph0, sup_comm, ← sup_assoc]

@[simp]
theorem cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R := by
  have := lift_mk_eq'.2 ⟨show (FreeMonoid X →₀ R) ≃ R from Equiv.finsuppUnique⟩
  rw [lift_id'.{u, v}, lift_umax] at this
  rwa [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra]

@[nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1 := by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra, mk_eq_one]

theorem cardinalMk_le_max_lift :
    #(FreeAlgebra R X) ≤ Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

variable (X : Type u)

theorem cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀ := by
  simp

theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp

theorem cardinalMk_le_max : #(FreeAlgebra R X) ≤ #R ⊔ #X ⊔ ℵ₀ := by
  simpa using cardinalMk_le_max_lift R X

end FreeAlgebra

namespace Algebra

theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) ≤ lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s → A))
  rw [lift_umax, lift_id'.{v, u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) ≤ #R ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le R s

end Algebra
