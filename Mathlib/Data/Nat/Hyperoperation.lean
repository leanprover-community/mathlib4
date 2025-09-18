/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Eric Wieser
-/
import Mathlib.Tactic.Ring

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
