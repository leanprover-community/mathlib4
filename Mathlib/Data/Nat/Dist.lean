/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Distance function on ℕ

This file defines a simple distance function on naturals from truncated subtraction.
-/


namespace Nat

/-- Distance (absolute value of difference) between natural numbers. -/
def dist (n m : ℕ) :=
  n - m + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n := by simp [dist, add_comm]

@[simp]
theorem dist_self (n : ℕ) : dist n n = 0 := by simp [dist, tsub_self]

theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m := by unfold Nat.dist at h; cutsat

theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 := by unfold Nat.dist; cutsat

theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by unfold Nat.dist; cutsat

theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m := by
  unfold Nat.dist; cutsat

theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n := by unfold Nat.dist; cutsat
theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m := by unfold Nat.dist; cutsat
theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m := by unfold Nat.dist; cutsat
theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m := by unfold Nat.dist; cutsat

theorem dist_zero_right (n : ℕ) : dist n 0 = n := by unfold Nat.dist; cutsat
theorem dist_zero_left (n : ℕ) : dist 0 n = n := by unfold Nat.dist; cutsat

theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m := by
  unfold Nat.dist; cutsat

theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m := by
  unfold Nat.dist; cutsat

theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m := by
  unfold Nat.dist; cutsat

theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k := by
  unfold Nat.dist; cutsat

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]

theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]

theorem dist_eq_max_sub_min {i j : ℕ} : dist i j = (max i j) - min i j := by
  cases le_total i j <;> simp [Nat.dist, *]

theorem dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j := by unfold Nat.dist; cutsat

theorem dist_pos_of_ne {i j : Nat} (h : i ≠ j) : 0 < dist i j := by unfold Nat.dist; cutsat

end Nat
