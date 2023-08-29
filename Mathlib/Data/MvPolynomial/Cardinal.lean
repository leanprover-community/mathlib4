/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.SetTheory.Cardinal.Ordinal

#align_import data.mv_polynomial.cardinal from "leanprover-community/mathlib"@"3cd7b577c6acf365f59a6376c5867533124eff6b"

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `MvPolynomial.cardinal_mk_le_max`, which says that
the cardinality of `MvPolynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/


universe u v

open Cardinal

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

@[simp]
theorem cardinal_mk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ :=
  (mk_finsupp_lift_of_infinite _ R).trans <| by
    rw [mk_finsupp_nat, max_assoc, lift_max, lift_aleph0, max_comm]
    -- 🎉 no goals
#align mv_polynomial.cardinal_mk_eq_max_lift MvPolynomial.cardinal_mk_eq_max_lift

@[simp]
theorem cardinal_mk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = Cardinal.lift.{u} #R :=
  ((isEmptyRingEquiv R σ).toEquiv.trans Equiv.ulift.{u}.symm).cardinal_eq
#align mv_polynomial.cardinal_mk_eq_lift MvPolynomial.cardinal_mk_eq_lift

theorem cardinal_lift_mk_le_max {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) ≤
    max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ := by
  cases subsingleton_or_nontrivial R
  -- ⊢ #(MvPolynomial σ R) ≤ max (max (lift.{u, v} #R) (lift.{v, u} #σ)) ℵ₀
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
    -- 🎉 no goals
  cases isEmpty_or_nonempty σ
  -- ⊢ #(MvPolynomial σ R) ≤ max (max (lift.{u, v} #R) (lift.{v, u} #σ)) ℵ₀
  · exact cardinal_mk_eq_lift.trans_le (le_max_of_le_left <| le_max_left _ _)
    -- 🎉 no goals
  · exact cardinal_mk_eq_max_lift.le
    -- 🎉 no goals
#align mv_polynomial.cardinal_lift_mk_le_max MvPolynomial.cardinal_lift_mk_le_max

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

theorem cardinal_mk_eq_max [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max #R #σ) ℵ₀ := by simp
                                                   -- 🎉 no goals
#align mv_polynomial.cardinal_mk_eq_max MvPolynomial.cardinal_mk_eq_max

/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
theorem cardinal_mk_le_max : #(MvPolynomial σ R) ≤ max (max #R #σ) ℵ₀ :=
  cardinal_lift_mk_le_max.trans <| by rw [lift_id, lift_id]
                                      -- 🎉 no goals
#align mv_polynomial.cardinal_mk_le_max MvPolynomial.cardinal_mk_le_max

end MvPolynomial
