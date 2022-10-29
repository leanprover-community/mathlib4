/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Data.Int.Cast

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.basic`.
-/

@[simp, norm_cast]
theorem Int.cast_pow [Ring R] (n : ℤ) : ∀ m : ℕ, (↑(n ^ m) : R) = (n : R) ^ m
  | 0 => by rw [pow_zero, pow_zero, Int.cast_one]
  | n+1 => by rw [pow_succ, pow_succ, Int.cast_mul, Int.cast_pow _ n]

@[simp] theorem pow_eq {m : ℤ} {n : ℕ} : m.pow n = m ^ n := rfl
