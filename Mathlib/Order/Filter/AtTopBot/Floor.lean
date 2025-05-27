/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# `a * c ^ n < (n - d)!` holds true for sufficiently large `n`.
-/

open Filter
open scoped Nat

variable {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

theorem FloorSemiring.eventually_mul_pow_lt_factorial_sub (a c : K) (d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ ≤ |a * c ^ n| := le_abs_self _
    _ ≤ ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < (n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> try first | positivity | apply Nat.le_ceil
  · simp_rw [Nat.cast_mul, Nat.cast_pow]
