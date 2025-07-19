import Mathlib.Tactic.Simproc.Divisors
import Mathlib.NumberTheory.Primorial

open Nat

example :
    Nat.divisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855, 1710} := by
  simp only [Nat.divisors_ofNat]

example : Nat.divisors 57 = {1, 3, 19, 57} := by
  simp only [Nat.divisors_ofNat]

example : (Nat.divisors <| 6 !).card = 30 := by
  simp [Nat.divisors_ofNat, Nat.factorial_succ]

example : (Nat.divisors <| primorial 12).card = 32 := by
  --TODO(Paul-Lez): seems like we need a norm_num extension for computing `primorial`!
  have : primorial 12 = 2310 := rfl
  simp [Nat.divisors_ofNat, this]

example : (Nat.divisors <| 2^13).card = 14 := by
  simp [Nat.divisors_ofNat]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisors_ofNat]

/-- error: simp made no progress -/
#guard_msgs in
example (n : ℕ) (hn : n ≠ 0) : 1 ≤ Finset.card (Nat.divisors n) := by
  simp only [Nat.divisors_ofNat]

example :
    Nat.properDivisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855} := by
  simp only [Nat.properDivisors_ofNat]

example : Nat.properDivisors 57 = {1, 3, 19} := by
  simp only [Nat.properDivisors_ofNat]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisors_ofNat]
