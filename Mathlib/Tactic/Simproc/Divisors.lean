import Mathlib.NumberTheory.Divisors
import Mathlib.Lean.ToExpr
import Mathlib.Data.Finset.Sort
import Lean

open Lean Meta

simproc_decl Nat.divisorsEq (Nat.divisors _) := fun e => do
  unless e.isAppOfArity `Nat.divisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhs ← (n.divisors.sort (· ≤ ·)).toFinsetExpr (α := ℕ)
  /- The last two lines can be replace by `return .done {expr := rhs }` since the proof is `rfl`.
  Not sure what's best here. -/
  let pf ← Meta.mkDecideProof (← mkEq e rhs)
  return .done {expr := rhs, proof? := pf }


simproc_decl Nat.properDivisorsEq (Nat.properDivisors _) := fun e => do
  unless e.isAppOfArity `Nat.properDivisors 1 do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  let rhs ← (n.properDivisors.sort (· ≤ ·)).toFinsetExpr (α := ℕ)
  /- The last two lines can be replace by `return .done {expr := rhs }` since the proof is `rfl`.
  Not sure what's best here.-/
  let pf ← Meta.mkDecideProof (← mkEq e rhs)
  return .done {expr := rhs, proof? := pf }

example :
    Nat.divisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855, 1710} := by
  simp only [Nat.divisorsEq]

example : Nat.divisors 57 = {1, 3, 19, 57} := by
  simp only [Nat.divisorsEq]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisorsEq]

example :
    Nat.properDivisors 1710 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 19, 30, 38, 45, 57,
      90, 95, 114, 171, 190, 285, 342, 570, 855} := by
  simp only [Nat.properDivisorsEq]

example : Nat.properDivisors 57 = {1, 3, 19} := by
  simp only [Nat.properDivisorsEq]

example : 2 ≤ Finset.card (Nat.divisors 3) := by
  simp [Nat.divisorsEq]
