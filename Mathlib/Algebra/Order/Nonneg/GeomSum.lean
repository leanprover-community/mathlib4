/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Daniel Weber
-/

import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.GeomSum
/-!
# Partial sums of geometric series in semifields
-/


variable {α : Type*} [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

lemma Nonneg.geom₂_sum_mul {x y : α} (h : x < y) (n : ℕ) :
    (∑ i ∈ Finset.range n, y ^ i * x ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le h.le] using geom_sum₂_mul_add (y - x) x n

lemma Nonneg.geom_sum_mul_of_one_lt {x : α} (h : 1 < x) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  convert geom₂_sum_mul h n <;> simp

/--
`Nonneg.geom₂_sum_mul'` for `x > y` (the names of `x`, `y`, are swapped here)
-/
lemma Nonneg.geom₂_sum_mul' {x y : α} (h : x < y) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert geom₂_sum_mul h n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  omega

lemma Nonneg.geom_sum_mul_of_lt_one {x : α} (h : x < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  convert geom₂_sum_mul' h n <;> simp

lemma Nonneg.geom₂_sum_of_lt {x y : α} (h : x < y) (n : ℕ) :
    ∑ i ∈ Finset.range n, y ^ i * x ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom₂_sum_mul h n)

/--
`Nonneg.geom₂_sum_of_lt` for `x > y` (the names of `x`, `y`, are swapped here)
-/
lemma Nonneg.geom₂_sum_of_lt' {x y : α} (h : x < y) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom₂_sum_mul' h n)

lemma Nonneg.geom_sum_of_one_lt {a : α} (h : 1 < a) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i = (a ^ n - 1) / (a - 1) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_lt h n)

lemma Nonneg.geom_sum_of_lt_one {a : α} (h : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i = (1 - a ^ n) / (1 - a) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_lt_one h n)
