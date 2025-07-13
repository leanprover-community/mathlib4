/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Bhavik Mehta
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Util.Qq
import Mathlib.Data.Finset.Sort

/-! # Divisor Simprocs

This file implements simprocs to compute various objects related to divisors:
- `Nat.divisorsEq`: computes `Nat.divisors n` for explicit values of `n`
- `Nat.properDivisorsEq`: computes `Nat.properDivisors n` for explicit values of `n`

-/

--TODO: these simprocs can probably be made a lot more efficient. See the discussion in #23026.

open Lean Meta Qq

/-- The `Nat.divisorsEq` computes the finset `Nat.divisors n` when `n` is a natural number
literal. -/
simproc_decl Nat.divisorsEq (Nat.divisors _) := fun e => do
  unless e.isAppOfArity `Nat.divisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhsListQ : List Q(ℕ) := (n.divisors.sort (· ≤ ·)).map fun n => (Lean.toExpr n : Q(ℕ))
  let rhs := mkSetLiteralQ q(Finset ℕ) rhsListQ
  return .done {expr := rhs }

/-- The `Nat.properDivisorsEq ` computes the finset `Nat.properDivisorsEq  n` when `n` is a natural
number literal. -/
simproc_decl Nat.properDivisorsEq (Nat.properDivisors _) := fun e => do
  unless e.isAppOfArity `Nat.properDivisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhsListQ : List Q(ℕ) := (n.properDivisors.sort (· ≤ ·)).map fun n => (Lean.toExpr n : Q(ℕ))
  let rhs := mkSetLiteralQ q(Finset ℕ) rhsListQ
  return .done {expr := rhs }
