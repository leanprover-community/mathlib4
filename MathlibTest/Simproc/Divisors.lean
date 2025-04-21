import Mathlib.Tactic.Simproc.Divisors

open Nat

example : Nat.divisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855, 1710} := by
  simp only [Nat.divisorsEq]

example : Nat.divisors 57 = {1, 3, 19, 57} := by
  simp only [Nat.divisorsEq]

#eval  (Nat.divisors <| 6 !).card

example : (Nat.divisors <| 6 !).card = 30 := by
  simp [Nat.divisorsEq, Nat.factorial_succ]

example : (Nat.divisors <| 2^20).card = 21 := by
  simp [Nat.divisorsEq, Nat.factorial_succ]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisorsEq]

/-- error: simp made no progress -/
#guard_msgs in
example (n : ℕ) (hn : n ≠ 0) : 1 ≤ Finset.card (Nat.divisors n) := by
  simp only [Nat.divisorsEq]

example :
    Nat.properDivisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855} := by
  simp only [Nat.properDivisorsEq]

example : Nat.properDivisors 57 = {1, 3, 19} := by
  simp only [Nat.properDivisorsEq]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisorsEq]
