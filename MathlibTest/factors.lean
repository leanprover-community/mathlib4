import Mathlib.Tactic.Simproc.Factors

example : Nat.primeFactorsList 0 = [] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 1 = [] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 2 = [2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 3 = [3] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 4 = [2, 2] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 12 = [2, 2, 3] := by simp only [Nat.primeFactorsList_ofNat]
example : Nat.primeFactorsList 221 = [13, 17] := by simp only [Nat.primeFactorsList_ofNat]
