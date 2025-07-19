/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Bhavik Mehta
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Util.Qq
import Mathlib.Data.Finset.Sort

/-! # Divisor Simprocs

This file implements (d)simprocs to compute various objects related to divisors:
- `Nat.divisorsEq`: computes `Nat.divisors n` for explicit values of `n`
- `Nat.properDivisorsEq`: computes `Nat.properDivisors n` for explicit values of `n`

-/

open Lean Meta Qq

/-- The `Nat.divisorsEq` computes the finset `Nat.divisors n` when `n` is a natural number
literal. -/
dsimproc_decl Nat.divisors_ofNat (Nat.divisors _) := fun e => do
  unless e.isAppOfArity `Nat.divisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return mkSetLiteralQ q(Finset ℕ) <| (n.divisors.sort (· ≤ ·)).map fun n => (Lean.toExpr n : Q(ℕ))

/-- Compute the finset `Nat.properDivisorsEq n` when `n` is a numeral;
for instance, this simplifies `Nat.properDivisorsEq 12` to `{1, 2, 3, 4, 6}`. -/
dsimproc_decl Nat.properDivisors_ofNat (Nat.properDivisors _) := fun e => do
  unless e.isAppOfArity `Nat.properDivisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhsListQ : List Q(ℕ) := (n.properDivisors.sort (· ≤ ·)).map fun n => (Lean.toExpr n : Q(ℕ))
  let rhs := mkSetLiteralQ q(Finset ℕ) rhsListQ
  return .done rhs
