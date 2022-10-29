/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute

/-!
### Monoids
-/

section Monoid

variable [Monoid M]

@[simp] theorem pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, mul_one]

@[simp] theorem one_pow (n : ℕ) : (1 : M) ^ n = 1 := by
  induction n <;> simp [*, pow_succ]

theorem pow_add (a : M) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n with n ih
  · rw [Nat.add_zero, pow_zero, mul_one]
  · rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', Nat.add_assoc]

theorem pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with n ih
  · rw [Nat.mul_zero, pow_zero, pow_zero]
  · rw [Nat.mul_succ, pow_add, pow_succ', ih]

theorem Commute.mul_pow {a b : M} (h : Commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, pow_zero, one_mul]
  · simp only [pow_succ, ih, ← mul_assoc, (h.pow_left n).right_comm]

end Monoid

/-!
### Commutative monoids
-/

section CommMonoid

variable [CommMonoid M]

theorem mul_pow (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_pow n

end CommMonoid
