/- Project Euler Problem 3: Largest prime factor
The prime factors of 13195 are 5, 7, 13 and 29.
What is the largest prime factor of the number 600851475143 ?
 -/


import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Finset.Sort

def getValues (s : Finset ℕ) : List ℕ :=
  s.sort (· ≤ ·)

def solution : Nat :=
  let factors := getValues (Nat.primeFactors 600_851_475_143)
  factors.max?.getD 0

#eval solution

---


def primeFactors (n : Nat) : List Nat :=
  let rec factors (fuel n d : Nat) : List Nat :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if n < 2 then []
      else if n % d == 0 then d :: factors fuel (n / d) d
      else factors fuel n (d + 1)
  factors n n 2

#eval primeFactors 13195

#eval primeFactors 600851475143

#check primeFactors 13195 == [5, 7, 13, 29]


def largestPrimeFactor (n : Nat) : Option Nat :=
  (primeFactors n).max?.getD 1

#eval (primeFactors 600851475143).max (by decide)

#eval largestPrimeFactor 600851475143
