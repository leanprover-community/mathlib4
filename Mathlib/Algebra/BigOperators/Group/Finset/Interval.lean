/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Zify

/-!
# Sums/products over integer intervals

This file contains some lemmas about sums and products over integer intervals `Ixx`.

-/

namespace Finset

@[to_additive]
lemma prod_Icc_of_even_eq_range {α : Type*} [CommGroup α] {f : ℤ → α} (hf : f.Even) (N : ℕ) :
    ∏ m ∈ Icc (-N : ℤ) N, f m = (∏ m ∈ range (N + 1), f m) ^ 2 / f 0 := by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, Icc_succ_succ, prod_union (by simp), prod_pair (by omega), ih,
      prod_range_succ _ (N + 1), hf, ← pow_two, div_mul_eq_mul_div, ← mul_pow, Nat.cast_succ]

@[to_additive]
lemma prod_Icc_eq_prod_Ico_mul {α : Type*} [CommMonoid α] (f : ℤ → α) {l u : ℤ}
    (h : l ≤ u) : ∏ m ∈ Icc l u, f m = (∏ m ∈ Ico l u, f m) * f u := by
  simp [Icc_eq_cons_Ico h, mul_comm]

@[to_additive]
lemma prod_Icc_succ_eq_mul_endpoints {R : Type*} [CommGroup R] (f : ℤ → R) {N : ℕ} :
    ∏ m ∈ Icc (-(N + 1) : ℤ) (N + 1), f m =
    f (N + 1) * f (-(N + 1) : ℤ) * ∏ m ∈ Icc (-N : ℤ) N, f m := by
  induction N
  · rw [Icc_succ_succ]
    simp only [CharP.cast_eq_zero, neg_zero, Icc_self, zero_add, Int.reduceNeg, union_insert,
      union_singleton, mem_insert, reduceCtorEq, mem_singleton, neg_eq_zero, one_ne_zero, or_self,
      not_false_eq_true, prod_insert, prod_singleton]
    grind
  · rw [Icc_succ_succ, prod_union (by simp)]
    grind

end Finset
