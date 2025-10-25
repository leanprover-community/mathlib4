/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Andreas Gittis
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for `Nat.log` and `Nat.clog`

This module defines `norm_num` extensions for `Nat.log` and `Nat.clog`.
-/

namespace Mathlib.Meta.NormNum

open Qq Lean Elab.Tactic

private lemma nat_log_zero (n : Nat) : Nat.log 0 n = 0 := Nat.log_zero_left n
private lemma nat_log_one (n : Nat) : Nat.log 1 n = 0 := Nat.log_one_left n

private lemma nat_log_helper0 (b n : Nat) (hl : Nat.blt n b = true) :
    Nat.log b n = 0 := by
  rw [Nat.blt_eq] at hl
  simp [hl]

private lemma nat_log_helper (b n k : Nat)
    (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt n (b ^ (k + 1)) = true) :
    Nat.log b n = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

private theorem isNat_log : {b nb n nn k : ℕ} → IsNat b nb → IsNat n nn →
    Nat.log nb nn = k → IsNat (Nat.log b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en`, returns `Nat.log eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
def proveNatLog (eb en : Q(ℕ)) : (ek : Q(ℕ)) × Q(Nat.log $eb $en = $ek) :=
  match eb.natLit!, en.natLit! with
  | 0, _ => have : $eb =Q nat_lit 0 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_zero $en)⟩
  | 1, _ => have : $eb =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 0), q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en $hh)⟩
    else
      let k := Nat.log b n
      have ek : Q(ℕ) := mkRawNatLit k
      have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
      have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
      ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

/--
Evaluates the `Nat.log` function.
-/
@[norm_num Nat.log _ _]
def evalNatLog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(ℕ)) (n : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sℕ ek pf'

private lemma nat_clog_zero_left (b n : Nat) (hb : Nat.ble b 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_left_le_one (Nat.le_of_ble_eq_true hb) n
private lemma nat_clog_zero_right (b n : Nat) (hn : Nat.ble n 1 = true) :
    Nat.clog b n = 0 := Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b

theorem nat_clog_helper {b m n : ℕ} (hb : Nat.blt 1 b = true)
    (h₁ : Nat.blt (b ^ m) n = true) (h₂ : Nat.ble n (b ^ (m + 1)) = true) :
    Nat.clog b n = m + 1 := by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq, ← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq, ← Nat.clog_le_iff_le_pow hb] at h₂
  cutsat

private theorem isNat_clog : {b nb n nn k : ℕ} → IsNat b nb → IsNat n nn →
    Nat.clog nb nn = k → IsNat (Nat.clog b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en`, returns `Nat.clog eb en`
as a natural number literal and an equality proof.
Panics if `ex` or `en` aren't natural number literals.
-/
def proveNatClog (eb en : Q(ℕ)) : (ek : Q(ℕ)) × Q(Nat.clog $eb $en = $ek) :=
  let b := eb.natLit!
  let n := en.natLit!
  if _ : b ≤ 1 then
    have h : Q(Nat.ble $eb 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_left $eb $en $h)⟩
  else if _ : n ≤ 1 then
    have h : Q(Nat.ble $en 1 = true) := reflBoolTrue
    ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en $h)⟩
  else
    match h : Nat.clog b n with
    | 0 => False.elim <|
      Nat.ne_of_gt (Nat.clog_pos (by cutsat) (by cutsat)) h
    | k + 1 =>
      have ek : Q(ℕ) := mkRawNatLit k
      have ek1 : Q(ℕ) := mkRawNatLit (k + 1)
      have _ : $ek1 =Q $ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      ⟨ek1, q(nat_clog_helper $hb $hl $hh)⟩

/--
Evaluates the `Nat.clog` function.
-/
@[norm_num Nat.clog _ _]
def evalNatClog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(ℕ)) (n : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  let ⟨ek, pf⟩ := proveNatClog eb en
  let pf' : Q(IsNat (Nat.clog $b $n) $ek) := q(isNat_clog $pb $pn $pf)
  return .isNat sℕ ek pf'

end Mathlib.Meta.NormNum
