/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.GCD

/-! # `norm_num` extension for `IsSquare`

This module defines a `norm_num` extension for `IsSquare x` for `x` a `Nat`, `Int`, or `Rat`.
Depends on the `Nat.sqrt` extension.

-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

section lemmas

theorem nat_isSquare_helper {x y : ℕ} (hy : x.sqrt = y)
    (hxz : Nat.beq x (y * y) = false) : ¬IsSquare x := by
  intro h
  apply Nat.ne_of_beq_eq_false hxz
  rw [← hy, eq_comm, ← Nat.exists_mul_self]
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr.symm⟩

theorem isSquare_of_isNat_nat : {x nx : ℕ} → IsNat x nx → IsSquare nx → IsSquare x
  | _, _, ⟨rfl⟩, h => h

theorem not_isSquare_of_isNat_nat : {x nx : ℕ} → IsNat x nx → ¬IsSquare nx → ¬IsSquare x
  | _, _, ⟨rfl⟩, h => h

theorem isSquare_of_isNat_int {x : ℤ} {nx : ℕ}
    (hx : IsNat x nx) (hnx : IsSquare nx) : IsSquare x := by
  rcases hx with ⟨rfl⟩
  obtain ⟨y, hy⟩ := hnx
  exact ⟨y, by simp [hy]⟩

theorem not_isSquare_of_isNat_int {x : ℤ} {nx : ℕ}
    (hx : IsNat x nx) (hnx : ¬IsSquare nx) : ¬IsSquare x := by
  rcases hx with ⟨rfl⟩
  rintro ⟨y, hy⟩
  apply hnx
  exact ⟨y.natAbs, (Int.natAbs_mul_natAbs_eq hy.symm).symm⟩

theorem not_isSquare_of_isNegOfNat {x : ℤ} {nx : ℕ}
    (hx : IsInt x (Int.negOfNat nx.succ)) : ¬IsSquare x := by
  rcases hx with ⟨rfl⟩
  rintro ⟨y, hy⟩
  rw [← Int.natAbs_mul_self] at hy
  cases hy

theorem isSquare_rat_eq {x : ℚ} : IsSquare x = (IsSquare x.num ∧ IsSquare x.den) :=
  propext Rat.isSquare_iff

end lemmas

/-- Given the natural number literal `ex`, returns a proof that it's a square
or a proof that it's not. Panics if `ex` isn't a natural number literal. -/
def proveIsSquareNat (ex : Q(ℕ)) : Q(IsSquare $ex) ⊕ Q(¬IsSquare $ex) :=
  let ⟨ey, pfy⟩ := proveNatSqrt ex
  let x := ex.natLit!
  let y := ey.natLit!
  if x = y * y then
    have : ($ey * $ey) =Q $ex := ⟨⟩
    .inl q(⟨$ey, Eq.refl $ex⟩)
  else
    have ne : Q(Nat.beq $ex ($ey * $ey) = false) := reflBoolFalse
    .inr q(nat_isSquare_helper $pfy $ne)

/-- `norm_num` extension that proves `IsSquare x` for `x : ℕ`. -/
@[norm_num IsSquare (_ : ℕ)]
def evalIsSquareNat : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  let ~q(IsSquare ($x : ℕ)) := e | failure
  let ⟨ex, px⟩ ← deriveNat x q(instAddMonoidWithOneNat)
  match proveIsSquareNat ex with
  | .inl pf => return .isTrue q(isSquare_of_isNat_nat $px $pf)
  | .inr pf => return .isFalse q(not_isSquare_of_isNat_nat $px $pf)

/-- `norm_num` extension that proves `IsSquare x` for `x : ℤ`. -/
@[norm_num IsSquare (_ : ℤ)]
def evalIsSquareInt : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  let ~q(IsSquare ($x : ℤ)) := e | failure
  match ← derive (α := q(ℤ)) x with
  | .isNat _ nx px =>
    assumeInstancesCommute
    match proveIsSquareNat nx with
    | .inl pf => return .isTrue q(isSquare_of_isNat_int $px $pf)
    | .inr pf => return .isFalse q(not_isSquare_of_isNat_int $px $pf)
  | .isNegNat _ nx px =>
    assumeInstancesCommute
    match nx.natLit! with
    | 0 => failure
    | .succ m =>
      have m : Q(Nat) := mkRawNatLit m
      have : Nat.succ $m =Q $nx := ⟨⟩
      return .isFalse q(not_isSquare_of_isNegOfNat $px)
  | _ => failure

/-- `norm_num` extension that proves `IsSquare x` for `x : ℚ`.
Depends on the extensions for `Rat.num` and `Rat.den`. -/
@[norm_num IsSquare (_ : ℚ)]
def evalIsSquareRat : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  let ~q(IsSquare ($x : ℚ)) := e | failure
  let r ← derive q(IsSquare ($x).num ∧ IsSquare ($x).den)
  return r.eqTrans q(isSquare_rat_eq)

end NormNum

end Tactic
