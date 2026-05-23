/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Results on `MvPolynomial.expand`

In this file we prove results about `MvPolynomial.expand` that require more than the basic API
available in `Mathlib.Algebra.*`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

theorem map_frobenius_expand {f : MvPolynomial σ R} :
    (f.expand p).map (frobenius R p) = f ^ p :=
  f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

@[deprecated (since := "2025-12-27")]
alias expand_char := map_frobenius_expand

theorem map_iterateFrobenius_expand (f : MvPolynomial σ R) (n : ℕ) :
    map (iterateFrobenius R p n) (expand (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

@[deprecated (since := "2025-12-27")]
alias map_expand_pow_char := map_iterateFrobenius_expand

end MvPolynomial
