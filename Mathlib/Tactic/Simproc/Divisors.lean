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
  let pf ← Meta.mkDecideProof (← mkEq e rhs)
  return .done {expr := rhs, proof? := pf }

/-- The `Nat.properDivisorsEq ` computes the finset `Nat.properDivisorsEq  n` when `n` is a natural
number literal. -/
simproc_decl Nat.properDivisorsEq (Nat.properDivisors _) := fun e => do
  unless e.isAppOfArity `Nat.properDivisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhsListQ : List Q(ℕ) := (n.properDivisors.sort (· ≤ ·)).map fun n => (Lean.toExpr n : Q(ℕ))
  let rhs := mkSetLiteralQ q(Finset ℕ) rhsListQ
  let pf ← Meta.mkDecideProof (← mkEq e rhs)
  return .done {expr := rhs, proof? := pf }

example : Nat.divisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855, 1710} := by
  simp only [Nat.divisorsEq]

example : Nat.divisors 57 = {1, 3, 19, 57} := by
  simp only [Nat.divisorsEq]

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
