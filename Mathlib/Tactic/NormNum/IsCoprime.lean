/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD

/-! # `norm_num` extension for `IsCoprime`

This module defines a `norm_num` extension for `IsCoprime` over `ℤ`.

(While `IsCoprime` is defined over `ℕ`, since it uses Bezout's identity with `ℕ` coefficients
it does not correspond to the usual notion of coprime.)
-/

public meta section

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

theorem int_not_isCoprime_helper (x y : ℤ) (d : ℕ) (hd : Int.gcd x y = d)
    (h : Nat.beq d 1 = false) : ¬ IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one, hd]
  exact Nat.ne_of_beq_eq_false h

theorem isInt_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → IsCoprime nx ny → IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isInt_not_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → ¬ IsCoprime nx ny → ¬ IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

/-- Evaluates `IsCoprime` for the given integer number literals.
Panics if `ex` or `ey` aren't integer number literals. -/
def proveIntIsCoprime (ex ey : Q(ℤ)) : Q(IsCoprime $ex $ey) ⊕ Q(¬ IsCoprime $ex $ey) :=
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)

/-- Evaluates the `IsCoprime` predicate over `ℤ`. -/
@[norm_num IsCoprime (_ : ℤ) (_ : ℤ)]
def evalIntIsCoprime : NormNumExt where eval {_ _} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'

end NormNum

end Tactic
