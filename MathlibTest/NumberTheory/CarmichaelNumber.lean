import Mathlib.NumberTheory.CarmichaelNumber

open Nat

example : IsCarmichael 561 := by norm_num1
example : IsCarmichael 1105 := by norm_num1
example : IsCarmichael 1729 := by norm_num1
example : IsCarmichael 2465 := by norm_num1
example : IsCarmichael 8911 := by norm_num1
example : IsCarmichael 41041 := by norm_num1
example : IsCarmichael 825265 := by norm_num1
example : IsCarmichael 321197185 := by norm_num1
example : IsCarmichael 2301745249 := by norm_num1
example : IsCarmichael 9999109081 := by norm_num1
example : IsCarmichael (500 + 61) := by norm_num1

example : ¬ IsCarmichael 0 := by norm_num1
example : ¬ IsCarmichael 1 := by norm_num1
example : ¬ IsCarmichael 2 := by norm_num1
example : ¬ IsCarmichael 3 := by norm_num1
example : ¬ IsCarmichael 4 := by norm_num1
example : ¬ IsCarmichael 15 := by norm_num1
example : ¬ IsCarmichael 560 := by norm_num1
example : ¬ IsCarmichael 562 := by norm_num1
example : ¬ IsCarmichael 1683 := by norm_num1
example : ¬ IsCarmichael 1000003 := by norm_num1
example : ¬ IsCarmichael (561 * 9) := by norm_num1
-- even
example : ¬ IsCarmichael 6 := by norm_num1
example : ¬ IsCarmichael (2 * 1000003) := by norm_num1
-- repeated prime factor
example : ¬ IsCarmichael 9 := by norm_num1
example : ¬ IsCarmichael (7 * 7 * 1000003) := by norm_num1
-- Korselt's criterion fails
example : ¬ IsCarmichael 15 := by norm_num1
example : ¬ IsCarmichael (3 * 1000003) := by norm_num1
-- Korselt's criterion fails on the last prime factor
example : ¬ IsCarmichael (3 * 11 * 17 * 241) := by norm_num1

example (n : ℕ) (hn : n < 561) : ¬ IsCarmichael n := by interval_cases n <;> norm_num1

/-! ### Decidability instance -/

#guard (List.range 20000).filter IsCarmichael =
  [561, 1105, 1729, 2465, 2821, 6601, 8911, 10585, 15841]

example : IsCarmichael 561 := by decide
example : IsCarmichael 8911 := by decide
example : ¬ IsCarmichael 562 := by decide
example : ¬ IsCarmichael 563 := by decide
example : ¬ IsCarmichael 1683 := by decide
example : IsCarmichael 2301745249 := by decide +kernel
example : ¬ IsCarmichael 1000003 := by decide +kernel
