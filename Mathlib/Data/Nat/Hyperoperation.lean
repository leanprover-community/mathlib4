/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Eric Wieser
-/
module

public import Mathlib.Tactic.NormNum.Pow

import Mathlib.Algebra.Order.Ring.Nat

/-!
# Hyperoperation sequence

This file defines the Hyperoperation sequence.
`hyperoperation 0 m k = k + 1`
`hyperoperation 1 m k = m + k`
`hyperoperation 2 m k = m * k`
`hyperoperation 3 m k = m ^ k`
`hyperoperation (n + 3) m 0 = 1`
`hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k)`

## References

* <https://en.wikipedia.org/wiki/Hyperoperation>

## Tags

hyperoperation
-/

@[expose] public section


/-- Implementation of the hyperoperation sequence
where `hyperoperation n m k` is the `n`th hyperoperation between `m` and `k`.
-/
def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)

attribute [local grind] hyperoperation

-- Basic hyperoperation lemmas
@[simp, grind =]
theorem hyperoperation_zero (m k : ℕ) : hyperoperation 0 m k = k + 1 := by
  grind

@[grind =]
theorem hyperoperation_ge_three_eq_one (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 := by
  grind

@[grind =]
theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  grind

-- Interesting hyperoperation lemmas
@[simp, grind =]
theorem hyperoperation_one (m k : ℕ) : hyperoperation 1 m k = m + k := by
  induction k with grind

@[simp, grind =]
theorem hyperoperation_two (m k : ℕ) : hyperoperation 2 m k = m * k := by
  induction k with grind

@[simp, grind =]
theorem hyperoperation_three (m k : ℕ) : hyperoperation 3 m k = m ^ k := by
  induction k with grind

@[grind =]
theorem hyperoperation_ge_two_eq_self (n m : ℕ) : hyperoperation (n + 2) m 1 = m := by
  induction n with grind

@[grind =]
theorem hyperoperation_two_two_eq_four (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 := by
  induction n with grind

@[grind =]
theorem hyperoperation_ge_three_one (n k : ℕ) : hyperoperation (n + 3) 1 k = 1 := by
  induction n generalizing k with grind [cases Nat]

@[grind =]
theorem hyperoperation_ge_four_zero (n k : ℕ) :
    hyperoperation (n + 4) 0 k = if Even k then 1 else 0 := by
  induction k with grind

theorem hyperoperation_eq_zero_iff (n m k : ℕ) :
    hyperoperation n m k = 0 ↔
      (n = 1 ∧ m = 0 ∧ k = 0) ∨ (n = 2 ∧ (m = 0 ∨ k = 0))
        ∨ (n = 3 ∧ m = 0 ∧ k ≠ 0) ∨ (4 ≤ n ∧ m = 0 ∧ Odd k) := by
  induction n generalizing m k with
  | zero =>
    simp
  | succ n ih =>
    match m, n, k with
    | 0, 0, _ => simp
    | 0, 1, _ => simp
    | 0, 2, _ => simp
    | 0, _ + 3, _ => simp [hyperoperation_ge_four_zero]
    | m + 1, 0, 0 => simp
    | m + 1, 1, 0 => simp
    | m + 1, n + 2, 0 => simp [hyperoperation]
    | m + 1, _, k + 1 => grind

theorem hyperoperation_mono_second_third (n a b c d : ℕ) (ha : a ≠ 0) (ac : a ≤ c) (bd : b ≤ d) :
    hyperoperation n a b ≤ hyperoperation n c d := by
  induction n generalizing a b c d with
  | zero =>
    simp [bd]
  | succ n hn =>
    induction d generalizing b with
    | zero =>
      simp_all only [nonpos_iff_eq_zero]
      match n with
      | 0 => simp [ac]
      | 1 => simp
      | n + 2 => rw [hyperoperation_ge_three_eq_one, hyperoperation_ge_three_eq_one]
    | succ d hd =>
      match b, n, c with
      | 0, 0, _ => simp; lia
      | 0, 1, _ => simp
      | 0, n + 2, c =>
        simp [hyperoperation_ge_three_eq_one, Nat.one_le_iff_ne_zero, hyperoperation_eq_zero_iff,
          show c ≠ 0 by grind]
      | b + 1, _, 0 => simp_all
      | b + 1, _, c + 1 =>
        rw [hyperoperation, hyperoperation]
        exact hn a _ _ _ ha ac (hd b (Nat.le_of_succ_le_succ bd))
