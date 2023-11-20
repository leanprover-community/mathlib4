/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Std.Data.Nat.Lemmas
import Mathlib.Tactic.NormNum

/-! # `norm_num` extension for `Nat` divisibility

This module defines a `norm_num` extension for `n ∣ m` for `n m : Nat`.
-/

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

theorem nat_dvd_helper (x y : ℕ) (h : y % x = 0) : x ∣ y := by
  rwa [Nat.dvd_iff_mod_eq_zero]

theorem nat_not_dvd_helper (x y : ℕ) (h : Nat.beq (y % x) 0 = false) : ¬ x ∣ y := by
  have := Nat.ne_of_beq_eq_false h
  rwa [Nat.dvd_iff_mod_eq_zero]

theorem isNat_dvd : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → nx ∣ ny → x ∣ y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isNat_not_dvd : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → ¬ nx ∣ ny → ¬ x ∣ y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem int_dvd_helper {x y : ℤ} {x' y' : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : x' ∣ y') : x ∣ y := by
  subst_vars
  simpa only [Nat.isUnit_iff, Int.natAbs_dvd_natAbs] using h

theorem int_not_dvd_helper {x y : ℤ} {x' y' : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : ¬ x' ∣ y') : ¬ x ∣ y := by
  subst_vars
  simpa only [Nat.isUnit_iff, Int.natAbs_dvd_natAbs] using h

theorem isInt_dvd : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → nx ∣ ny → x ∣ y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isInt_not_dvd : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → ¬ nx ∣ ny → ¬ x ∣ y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

/-- Evaluates `x ∣ y` for the given natural number literals.
Panics if `ex` or `ey` aren't natural number literals. -/
def proveNatDvd (ex ey : Q(ℕ)) : Q($ex ∣ $ey) ⊕ Q(¬ $ex ∣ $ey) :=
  let x := ex.natLit!
  let y := ey.natLit!
  let r := y % x
  if r == 0 then
    have pf : Q($ey % $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
    Sum.inl q(nat_dvd_helper $ex $ey $pf)
  else
    have pf : Q(Nat.beq ($ey % $ex) 0 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(nat_not_dvd_helper $ex $ey $pf)

/-- Evaluates the `(· ∣ ·)` relation over `ℕ`. -/
@[norm_num (_ : ℕ) ∣ (_ : ℕ)]
def evalNatDvd : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  match proveNatDvd ex ey with
  | .inl pf =>
    return .isTrue q(isNat_dvd $p $q $pf)
  | .inr pf =>
    return .isFalse q(isNat_not_dvd $p $q $pf)

/-- Evaluates `x ∣ y` for the given integer number literals.
Panics if `ex` or `ey` aren't integer literals. -/
def proveIntDvd (ex ey : Q(ℤ)) : Q($ex ∣ $ey) ⊕ Q(¬ $ex ∣ $ey) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  match proveNatDvd ex' ey' with
  | .inl pf => .inl q(int_dvd_helper $hx $hy $pf)
  | .inr pf => .inr q(int_not_dvd_helper $hx $hy $pf)

/-- Evaluates the `(· ∣ ·)` relation over `ℤ`. -/
@[norm_num (_ : ℤ) ∣ (_ : ℤ)]
def evalIntDvd : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Prop := ⟨⟩
  haveI' : $e =Q ($x ∣ $y) := ⟨⟩
  match proveIntDvd ex ey with
  | .inl pf => return .isTrue q(isInt_dvd $p $q $pf)
  | .inr pf => return .isFalse q(isInt_not_dvd $p $q $pf)

end NormNum

end Tactic
