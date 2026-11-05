module

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum.Pow

import Mathlib.Tactic.Primality

/-! # Tests for the `primality` tactic -/

/-! ## Lucas certificates

Proves `Nat.Prime p` by the Lucas test from a primitive root and certified prime factors of `p - 1`,
with each of the intermediate primes proved the same way with the same factor hints, unless the user
provides proofs.
-/

example : Nat.Prime 100000007 := by primality

example : Nat.Prime (10 ^ 9 + 7) := by primality

-- `p - 1 = 2 ^ 4 * 1031 ^ 2`, so Pollard's rho method finds the factor `1031` twice.
example : Nat.Prime 17007377 := by primality

/-- error: primality failed to find a witness for 100000000004900000000016761; provide the
certificate at `.witnesses […]` -/
#guard_msgs in
example : Nat.Prime (2 * 10000000000037 * 10000000000453 + 1) := by primality

example : Nat.Prime (2 * 10000000000037 * 10000000000453 + 1) := by
  primality (cert := .search { factors := [10000000000037] })

-- Pollard's rho method needs more than the default `2 ^ 17` steps to split
-- `10000003003 * 100000000000031`.
example : Nat.Prime (2 * 10000003003 * 100000000000031 + 1) := by
  primality (cert := .search { rhoSteps := 2 ^ 18 })

theorem prime_4398046517687 : Nat.Prime 4398046517687 := by primality

-- Takes an already proven prime as a hint.
example : Nat.Prime (2 * 4398046517687 * 10000000001437 + 1) := by
  primality [prime_4398046517687]

-- The same with a hypothesis.
example (h : Nat.Prime 4398046517687) : Nat.Prime (2 * 4398046517687 * 10000000001437 + 1) := by
  primality [h]

/-! ## Special primes -/

example : Nat.Prime (2 ^ 127 - 1) := by primality

-- Only the last 3 factors are required, but 8 are included so the producer is faster.
set_option exponentiation.threshold 521 in
example : Nat.Prime (2 ^ 521 - 1) := by
  primality (cert := .search { factors := [5746001, 7623851, 34110701, 308761441, 2400573761,
    65427463921, 108140989558681, 145295143558111] })

open Nat in
example : Nat.Prime (73 ! + 1) := by simp [Nat.factorial]; primality

/-! ## Certificates given by witnesses -/

example : Nat.Prime 65537 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2] }])

-- Repeated prime factors are deduplicated.
example : Nat.Prime 65537 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2] }])

-- `786433 - 1` and `3221225473 - 1` have the same prime factors, and `5` is a primitive root of
-- `3221225473` only, so `786433` takes the last entry.
example : Nat.Prime (72 * 786433 * 3221225473 + 1) := by
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 3, 786433, 3221225473] },
    .lucas { root := 5, primeFactors := [2, 3] },
    .lucas { root := 10, primeFactors := [2, 3] }])

-- Takes a proof that `786433` is prime as a hint, so that prime needs no entry.
example (h : Nat.Prime 786433) : Nat.Prime (72 * 786433 * 3221225473 + 1) := by
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 3, 786433, 3221225473] },
    .lucas { root := 5, primeFactors := [2, 3] }]) [h]

-- `1031` divides both `p - 1` and `2063 - 1`, so the tree meets it twice.
example : Nat.Prime 12761719 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 1031, 2063] },
    .lucas { root := 5, primeFactors := [2, 1031] },
    .lucas { root := 14, primeFactors := [2, 5, 103] }])

-- Curve25519's field prime
example : Nat.Prime (2 ^ 255 - 19) := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907] },
    .lucas { root := 2, primeFactors := [2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 75707, 72106336199, 1919519569386763] },
    .lucas { root := 10, primeFactors := [2, 3, 31, 107, 223, 4153, 430751] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 19, 47, 127, 8574133] },
    .lucas { root := 7, primeFactors := [2, 13, 2773320623] },
    .lucas { root := 5, primeFactors := [2, 2437, 569003] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 103, 991] },
    .lucas { root := 2, primeFactors := [2, 3, 43, 3727] },
    .lucas { root := 2, primeFactors := [2, 7, 97, 419] },
    .lucas { root := 17, primeFactors := [2, 5, 1723] },
    .lucas { root := 26, primeFactors := [2, 3, 7, 131] },
    .lucas { root := 2, primeFactors := [2, 37853] },
    .lucas { root := 2, primeFactors := [2, 32573] },
    .lucas { root := 2, primeFactors := [2, 59, 487] },
    .lucas { root := 2, primeFactors := [2, 9463] },
    .lucas { root := 2, primeFactors := [2, 17, 479] },
    .lucas { root := 3, primeFactors := [2, 3, 19, 83] },
    .lucas { root := 5, primeFactors := [2, 3, 173] },
    .lucas { root := 3, primeFactors := [2, 3, 23] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 29] },
    .lucas { root := 3, primeFactors := [2, 3, 7, 41] }])

/-! ## Errors -/

/-- error: n does not evaluate to a numeral; try simplifying it first -/
#guard_msgs in
example (n : ℕ) : Nat.Prime n := by primality

/-- error: primality failed to find a witness for 1000001; provide the certificate at
`.witnesses […]` -/
#guard_msgs in
example : Nat.Prime 1000001 := by primality

-- `2` is not a primitive root of `65537`, since `2 ^ 32 % 65537 = 1`.
/-- error: no provided witness certifies the primality of 65537 -/
#guard_msgs in
example : Nat.Prime 65537 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2] }])
