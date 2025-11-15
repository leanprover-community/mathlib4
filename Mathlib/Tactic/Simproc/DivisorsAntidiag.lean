/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau
-/
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Divisors

/-!
# Simproc for `Int.divisorsAntidiag`
-/

open
  Qq
  Lean
    Meta
      Simp
    Elab
      Term
    Parser
      Tactic

namespace Mathlib.Tactic.Simp

open Finset

/-- Given a natural number `n`, returns `(s, ⊢ Nat.divisorsAntidiagonal n = s)`. -/
def evalNatDivisorsAntidiag (n : ℕ) (en : Q(ℕ)) :
    MetaM ((l : Q(Finset (ℕ × ℕ))) × Q(Nat.divisorsAntidiagonal $en = $l)) := do
  match enl.natLit! with
  | 0 =>
    have _ : $enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
    let _ : $enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | _ => do
    have h2 : Q(IsNat 2 (nat_lit 2)) := q(⟨Eq.refl (nat_lit 2)⟩)
    let ⟨l, p⟩ ← evalPrimeFactorsListAux hn h2
    return ⟨l, q(($p).primeFactorsList_eq)⟩

/-- Given a natural number `n`, returns `(l, ⊢ Nat.primeFactorsList n = l)`. -/
def evalDivisorsAntidiag
    {en enl : Q(ℕ)} (hn : Q(IsNat $en $enl)) :
    MetaM ((l : Q(List ℕ)) × Q(Nat.primeFactorsList $en = $l)) := do
  match enl.natLit! with
  | 0 =>
    have _ : $enl =Q nat_lit 0 := ⟨⟩
    have hen : Q($en = 0) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_zero)⟩
  | 1 =>
    let _ : $enl =Q nat_lit 1 := ⟨⟩
    have hen : Q($en = 1) := q($(hn).out)
    return ⟨_, q($hen ▸ Nat.primeFactorsList_one)⟩
  | _ => do
    have h2 : Q(IsNat 2 (nat_lit 2)) := q(⟨Eq.refl (nat_lit 2)⟩)
    let ⟨l, p⟩ ← evalPrimeFactorsListAux hn h2
    return ⟨l, q(($p).primeFactorsList_eq)⟩

simproc divisors_antidiag (Int.divisorsAntidiag _) := fun e ↦ do
  let ⟨1, ~q(Finset (ℤ × ℤ)), ~q(Int.divisorsAntidiag <| OfNat.ofNat $e)⟩ ← inferTypeQ e
    | return .continue
  let ⟨l, p⟩ ← evalPrimeFactorsList hn
  return .done { expr := l, proof? := p }

example : Int.divisorsAntidiag 10 = {(-1, -1), (1, 1)} := by
  simp

end Mathlib.Tactic.Simp
