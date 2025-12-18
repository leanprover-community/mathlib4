/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Results on `MvPolynomial.expand`

In this file we prove results about `MvPolynomial.expand` that require more than the basic API
available in `Mathlib.Algebra.*`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

theorem expand_char {f : MvPolynomial σ R} :
    (f.expand p).map (frobenius R p) = f ^ p :=
  f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

theorem map_expand_char_pow (f : MvPolynomial σ R) (n : ℕ) :
    map (frobenius R p ^ n) (expand (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [RingHom.one_def, map_id]
  | succ _ n_ih =>
    symm
    rw [pow_succ, pow_mul, ← n_ih, ← expand_char, pow_succ', RingHom.mul_def, ← map_map, mul_comm,
      expand_mul, ← map_expand]

end MvPolynomial
