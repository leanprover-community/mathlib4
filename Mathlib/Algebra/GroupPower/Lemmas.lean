/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.GroupPower.Basic

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.basic`.

This is an ad-hoc port file.
-/

@[simp, norm_cast]
lemma Nat.cast_pow [Semiring R] {m n : ℕ} : (m ^ n).cast = (m.cast ^ n : R) := by
  induction n generalizing m <;> simp_all [Nat.pow_succ', _root_.pow_succ'', pow_zero]

@[simp, norm_cast]
theorem Int.cast_pow [Ring R] (n : ℤ) : ∀ m : ℕ, (↑(n ^ m) : R) = (n : R) ^ m
  | 0 => by rw [pow_zero, pow_zero, Int.cast_one]
  | n+1 => by rw [pow_succ, pow_succ, Int.cast_mul, Int.cast_pow _ n]

@[simp] theorem pow_eq {m : ℤ} {n : ℕ} : m.pow n = m ^ n := rfl

theorem nsmul_eq_mul' [Semiring R] (a : R) (n : ℕ) : n • a = a * n := by
  induction' n with n ih
  · rw [zero_nsmul, Nat.cast_zero, mul_zero]
  · rw [succ_nsmul', ih, Nat.cast_succ, mul_add, mul_one]

@[simp] theorem nsmul_eq_mul [Semiring R] (n : ℕ) (a : R) : n • a = n * a := by
  rw [nsmul_eq_mul', (n.cast_commute a).eq]
