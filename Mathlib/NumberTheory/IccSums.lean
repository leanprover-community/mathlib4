/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star

/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Icc (-N) N` used in the
definition of the Eisenstein series `E2`.

-/

open Finset

lemma Icc_succ_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n + 1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega

lemma sum_Icc_of_even_eq_range {α : Type*} [CommRing α] {f : ℤ → α} (hf : ∀ n, f n = f (-n))
    (N : ℕ) : ∑ m ∈  Finset.Icc (-N : ℤ) N, f m =  2 * ∑ m ∈ Finset.range (N + 1), f m  - f 0 := by
  induction N with
  | zero => simp [two_mul]
  | succ N ih =>
    have := Icc_succ_succ N
    simp only [neg_add_rev, Int.reduceNeg,  Nat.cast_add, Nat.cast_one] at *
    rw [this, Finset.sum_union (by simp), Finset.sum_pair (by omega), ih]
    nth_rw 2 [Finset.sum_range_succ]
    have HF := hf (N + 1)
    simp only [neg_add_rev, Int.reduceNeg] at HF
    rw [← HF]
    ring_nf
    norm_cast

@[to_additive]
lemma prod_Icc_eq_prod_Ico_succ {α : Type*} [CommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) : ∏ m ∈ Icc l u, f m = (∏ m ∈ Finset.Ico l u, f m) * f u := by
  simp [Finset.Icc_eq_cons_Ico h,Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, mul_comm]

lemma sum_Icc_add_endpoints {R : Type*} [AddCommGroup R] (f : ℤ → R) {N : ℕ}
    (hn : 1 ≤ N) : ∑ m ∈ Icc (-N : ℤ) N, f m =
    f N + f (-N : ℤ)  + ∑ m ∈ Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N
  · grind
  · zify
    rw [Icc_succ_succ, Finset.sum_union (by simp)]
    grind
