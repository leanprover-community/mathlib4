/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Eric Wieser
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Parity

#align_import data.nat.hyperoperation from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

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
-- porting note: termination_by was not required before port
def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)
  termination_by hyperoperation a b c => (a, b, c)
#align hyperoperation hyperoperation

-- Basic hyperoperation lemmas
@[simp]
theorem hyperoperation_zero (m : ℕ) : hyperoperation 0 m = Nat.succ :=
  funext fun k => by rw [hyperoperation, Nat.succ_eq_add_one]
                     -- 🎉 no goals
#align hyperoperation_zero hyperoperation_zero

theorem hyperoperation_ge_three_eq_one (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 := by
  rw [hyperoperation]
  -- 🎉 no goals
#align hyperoperation_ge_three_eq_one hyperoperation_ge_three_eq_one

theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  rw [hyperoperation]
  -- 🎉 no goals
#align hyperoperation_recursion hyperoperation_recursion

-- Interesting hyperoperation lemmas
@[simp]
theorem hyperoperation_one : hyperoperation 1 = (· + ·) := by
  ext m k
  -- ⊢ hyperoperation 1 m k = m + k
  induction' k with bn bih
  -- ⊢ hyperoperation 1 m Nat.zero = m + Nat.zero
  · rw [Nat.add_zero m, hyperoperation]
    -- 🎉 no goals
  · rw [hyperoperation_recursion, bih, hyperoperation_zero]
    -- ⊢ Nat.succ (m + bn) = m + Nat.succ bn
    exact Nat.add_assoc m bn 1
    -- 🎉 no goals
#align hyperoperation_one hyperoperation_one

@[simp]
theorem hyperoperation_two : hyperoperation 2 = (· * ·) := by
  ext m k
  -- ⊢ hyperoperation 2 m k = m * k
  induction' k with bn bih
  -- ⊢ hyperoperation 2 m Nat.zero = m * Nat.zero
  · rw [hyperoperation]
    -- ⊢ 0 = m * Nat.zero
    exact (Nat.mul_zero m).symm
    -- 🎉 no goals
  · rw [hyperoperation_recursion, hyperoperation_one, bih]
    -- ⊢ (fun x x_1 => x + x_1) m (m * bn) = m * Nat.succ bn
    -- porting note: was `ring`
    dsimp only
    -- ⊢ m + m * bn = m * Nat.succ bn
    nth_rewrite 1 [← mul_one m]
    -- ⊢ m * 1 + m * bn = m * Nat.succ bn
    rw [← mul_add, add_comm, Nat.succ_eq_add_one]
    -- 🎉 no goals
#align hyperoperation_two hyperoperation_two

@[simp]
theorem hyperoperation_three : hyperoperation 3 = (· ^ ·) := by
  ext m k
  -- ⊢ hyperoperation 3 m k = m ^ k
  induction' k with bn bih
  -- ⊢ hyperoperation 3 m Nat.zero = m ^ Nat.zero
  · rw [hyperoperation_ge_three_eq_one]
    -- ⊢ 1 = m ^ Nat.zero
    exact (pow_zero m).symm
    -- 🎉 no goals
  · rw [hyperoperation_recursion, hyperoperation_two, bih]
    -- ⊢ (fun x x_1 => x * x_1) m (m ^ bn) = m ^ Nat.succ bn
    exact (pow_succ m bn).symm
    -- 🎉 no goals
#align hyperoperation_three hyperoperation_three

theorem hyperoperation_ge_two_eq_self (n m : ℕ) : hyperoperation (n + 2) m 1 = m := by
  induction' n with nn nih
  -- ⊢ hyperoperation (Nat.zero + 2) m 1 = m
  · rw [hyperoperation_two]
    -- ⊢ (fun x x_1 => x * x_1) m 1 = m
    ring
    -- 🎉 no goals
  · rw [hyperoperation_recursion, hyperoperation_ge_three_eq_one, nih]
    -- 🎉 no goals
#align hyperoperation_ge_two_eq_self hyperoperation_ge_two_eq_self

theorem hyperoperation_two_two_eq_four (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 := by
  induction' n with nn nih
  -- ⊢ hyperoperation (Nat.zero + 1) 2 2 = 4
  · rw [hyperoperation_one]
    -- 🎉 no goals
  · rw [hyperoperation_recursion, hyperoperation_ge_two_eq_self, nih]
    -- 🎉 no goals
#align hyperoperation_two_two_eq_four hyperoperation_two_two_eq_four

theorem hyperoperation_ge_three_one (n : ℕ) : ∀ k : ℕ, hyperoperation (n + 3) 1 k = 1 := by
  induction' n with nn nih
  -- ⊢ ∀ (k : ℕ), hyperoperation (Nat.zero + 3) 1 k = 1
  · intro k
    -- ⊢ hyperoperation (Nat.zero + 3) 1 k = 1
    rw [hyperoperation_three]
    -- ⊢ (fun x x_1 => x ^ x_1) 1 k = 1
    dsimp
    -- ⊢ 1 ^ k = 1
    rw [one_pow]
    -- 🎉 no goals
  · intro k
    -- ⊢ hyperoperation (Nat.succ nn + 3) 1 k = 1
    cases k
    -- ⊢ hyperoperation (Nat.succ nn + 3) 1 Nat.zero = 1
    · rw [hyperoperation_ge_three_eq_one]
      -- 🎉 no goals
    · rw [hyperoperation_recursion, nih]
      -- 🎉 no goals
#align hyperoperation_ge_three_one hyperoperation_ge_three_one

theorem hyperoperation_ge_four_zero (n k : ℕ) :
    hyperoperation (n + 4) 0 k = if Even k then 1 else 0 := by
  induction' k with kk kih
  -- ⊢ hyperoperation (n + 4) 0 Nat.zero = if Even Nat.zero then 1 else 0
  · rw [hyperoperation_ge_three_eq_one]
    -- ⊢ 1 = if Even Nat.zero then 1 else 0
    simp only [even_zero, if_true]
    -- 🎉 no goals
  · rw [hyperoperation_recursion]
    -- ⊢ hyperoperation (n + 3) 0 (hyperoperation (n + 3 + 1) 0 kk) = if Even (Nat.su …
    rw [kih]
    -- ⊢ hyperoperation (n + 3) 0 (if Even kk then 1 else 0) = if Even (Nat.succ kk)  …
    simp_rw [Nat.even_add_one]
    -- ⊢ hyperoperation (n + 3) 0 (if Even kk then 1 else 0) = if ¬Even kk then 1 els …
    split_ifs
    -- ⊢ hyperoperation (n + 3) 0 1 = 0
    · exact hyperoperation_ge_two_eq_self (n + 1) 0
      -- 🎉 no goals
    · exact hyperoperation_ge_three_eq_one n 0
      -- 🎉 no goals
#align hyperoperation_ge_four_zero hyperoperation_ge_four_zero
