/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Andreas Gittis
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-! # `norm_num` extension for `Nat.log`

This module defines a `norm_num` extension for `Nat.log`.
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
  | 0, _ => show (ek : Q(ℕ)) × Q(Nat.log 0 $en = $ek) from ⟨mkRawNatLit 0, q(nat_log_zero $en)⟩
  | 1, _ => show (ek : Q(ℕ)) × Q(Nat.log 1 $en = $ek) from ⟨mkRawNatLit 0, q(nat_log_one $en)⟩
  | b, n =>
    if n < b then
      have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
      ⟨mkRawNatLit 0, q(nat_log_helper0 $eb $en $hh)⟩
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

end Mathlib.Meta.NormNum
