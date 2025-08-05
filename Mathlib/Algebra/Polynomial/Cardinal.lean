/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of Polynomial Ring

The result in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/


universe u

open Cardinal Polynomial

open Cardinal

namespace Polynomial

@[simp]
theorem cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max #R ℵ₀ :=
  (toFinsuppIso R).toEquiv.cardinal_eq.trans <| by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm]
    rfl

theorem cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) ≤ max #R ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le

end Polynomial
