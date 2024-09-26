/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Order.Filter.AtTopBot

/-!
# `a * c ^ n / (n - d)! < ε` holds true for sufficiently large `n`.
-/

open Filter
open scoped Nat

variable {K : Type*}

theorem FloorSemiring.eventually_mul_pow_lt_factorial_sub [LinearOrderedRing K] [FloorSemiring K]
    (a c : K) (d : ℕ) : ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ ≤ |a * c ^ n| := le_abs_self _
    _ ≤ ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < ↑(n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> try first | positivity | apply Nat.le_ceil
  · simp_rw [Nat.cast_mul, Nat.cast_pow]

theorem FloorSemiring.eventually_mul_pow_div_factorial_lt [LinearOrderedField K] [FloorSemiring K]
    (a c : K) (d : ℕ) {ε : K} (hε : 0 < ε) : ∀ᶠ n in atTop, a * c ^ n / (n - d)! < ε := by
  filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
  rw [mul_right_comm, mul_inv_lt_iff hε] at h
  rwa [div_lt_iff (Nat.cast_pos.mpr (Nat.factorial_pos _))]
