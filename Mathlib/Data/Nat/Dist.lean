/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical

/-!
#  Distance function on ℕ

This file defines a simple distance function on naturals from truncated subtraction.
-/


namespace Nat

/-- Distance (absolute value of difference) between natural numbers. -/
def dist (n m : ℕ) :=
  n - m + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n := by simp [dist, add_comm]

@[simp]
theorem dist_self (n : ℕ) : dist n n = 0 := by simp [dist, tsub_self]

theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m :=
  have : n - m = 0 := Nat.eq_zero_of_add_eq_zero_right h
  have : n ≤ m := tsub_eq_zero_iff_le.mp this
  have : m - n = 0 := Nat.eq_zero_of_add_eq_zero_left h
  have : m ≤ n := tsub_eq_zero_iff_le.mp this
  le_antisymm ‹n ≤ m› ‹m ≤ n›

theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 := by rw [h, dist_self]

theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by
  rw [dist, tsub_eq_zero_iff_le.mpr h, zero_add]

theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m := by
  rw [dist_comm]; apply dist_eq_sub_of_le h

theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n :=
  le_trans le_tsub_add (add_le_add_right (Nat.le_add_left _ _) _)

theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m := by rw [add_comm]; apply dist_tri_left

theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m := by rw [dist_comm]; apply dist_tri_left

theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m := by rw [dist_comm]; apply dist_tri_right

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
  Eq.trans (dist_eq_sub_of_le_right (zero_le n)) (tsub_zero n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
  Eq.trans (dist_eq_sub_of_le (zero_le n)) (tsub_zero n)

theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
  calc
    dist (n + k) (m + k) = n + k - (m + k) + (m + k - (n + k)) := rfl
    _ = n - m + (m + k - (n + k)) := by rw [@add_tsub_add_eq_tsub_right]
    _ = n - m + (m - n) := by rw [@add_tsub_add_eq_tsub_right]

theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m := by
  rw [add_comm k n, add_comm k m]; apply dist_add_add_right

theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m :=
  calc
    dist n k = dist (n + m) (k + m) := by rw [dist_add_add_right]
    _ = dist (k + l) (k + m) := by rw [h]
    _ = dist l m := by rw [dist_add_add_left]

theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k := by
  have : dist n m + dist m k = n - m + (m - k) + (k - m + (m - n)) := by
    simp [dist, add_comm, add_left_comm, add_assoc]
  rw [this, dist]
  exact add_le_add tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]

theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]

theorem dist_eq_max_sub_min {i j : ℕ} : dist i j = (max i j) - min i j :=
  Or.elim (lt_or_ge i j)
  (by intro h; rw [max_eq_right_of_lt h, min_eq_left_of_lt h, dist_eq_sub_of_le (Nat.le_of_lt h)])
  (by intro h; rw [max_eq_left h, min_eq_right h, dist_eq_sub_of_le_right h])

theorem dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j := by
  simp [dist, succ_sub_succ]

theorem dist_pos_of_ne {i j : Nat} (h : i ≠ j) : 0 < dist i j := by
  cases h.lt_or_gt with
  | inl h => rw [dist_eq_sub_of_le h.le]; apply tsub_pos_of_lt h
  | inr h => rw [dist_eq_sub_of_le_right h.le]; apply tsub_pos_of_lt h

end Nat
