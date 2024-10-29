/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Fintype.BigOperators

variable {α : Type*} [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

lemma Nonneg.geom_sum_of_one_lt {a : α} (h : 1 < a) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i = (a ^ n - 1) / (a - 1) := by
  apply eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (eq_tsub_of_add_eq _)
  simpa only [tsub_add_cancel_of_le h.le] using geom_sum_mul_add (a - 1) n

lemma Nonneg.geom_sum_of_lt_one {a : α} (h : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i = (1 - a ^ n) / (1 - a) := by
  apply eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (eq_tsub_of_add_eq _)
  suffices ∑ i ∈ Finset.range n, a ^ i = ∑ i ∈ Finset.range n, a ^ (n - 1 - i) by
    simpa only [tsub_add_cancel_of_le h.le, one_pow, one_mul, this] using
      geom_sum₂_mul_add (1 - a) a n
  let e : Fin n ≃ Fin n := Fin.rev_involutive.toPerm
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range, ← e.sum_comp]
  have (i : Fin n) : e i = n - 1 - i := by dsimp [e]; omega
  simp [this]
