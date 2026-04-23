/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finsupp
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `MvPolynomial.cardinalMk_le_max`, which says that
the cardinality of `MvPolynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/

public section


universe u v

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

-- We want this to have higher priority than `AddMonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`.
@[simp high]
theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by simp [sup_assoc]

-- We want this to have higher priority than `AddMonoidAlgebra.cardinalMk_eq_lift_of_fintype`.
@[simp high]
theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = lift.{u} #R := by simp

@[nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := mk_eq_one _


/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max` for the universe monomorphic version. -/
theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] :
    #(MvPolynomial σ R) ≤ lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by
  nontriviality R; cases isEmpty_or_nonempty σ <;> simp

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] : #(MvPolynomial σ R) = #R ⊔ #σ ⊔ ℵ₀ := by
  simp [sup_assoc]

theorem cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R := by simp

/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max_lift` for the universe polymorphic version. -/
theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ #R ⊔ #σ ⊔ ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by rw [lift_id, lift_id]

end MvPolynomial
