/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Bhavik Mehta
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Util.Qq

/-! # Divisor Simprocs

This file implements (d)simprocs to compute various objects related to divisors:
- `Nat.divisors_ofNat`: computes `Nat.divisors n` for explicit values of `n`
- `Nat.properDivisors_ofNat`: computes `Nat.properDivisors n` for explicit values of `n`

-/

open Lean Meta Simp Qq

/-- The dsimproc `Nat.divisors_ofNat` computes the finset `Nat.divisors n` when `n` is a
numeral. For instance, this simplifies `Nat.divisors 6` to `{1, 2, 3, 6}`. -/
dsimproc_decl Nat.divisors_ofNat (Nat.divisors _) := fun e => do
  unless e.isAppOfArity `Nat.divisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| mkSetLiteralQ q(Finset ℕ) <| ((unsafe n.divisors.val.unquot).map mkNatLit)

/-- The dsimproc `Nat.properDivisors_ofNat` computes the finset `Nat.properDivisors n` when
`n` is a numeral. For instance, this simplifies `Nat.properDivisors 12` to `{1, 2, 3, 4, 6}`. -/
dsimproc_decl Nat.properDivisors_ofNat (Nat.properDivisors _) := fun e => do
  unless e.isAppOfArity `Nat.properDivisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return unsafe .done <| mkSetLiteralQ q(Finset ℕ) <|
    ((unsafe n.properDivisors.val.unquot).map mkNatLit)
