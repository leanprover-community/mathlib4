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

namespace Tactic

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

lemma nat_log_helper (b n k : Nat)
    (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt n (b ^ (k + 1)) = true) :
    Nat.log b n = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

theorem isNat_log : {b nb n nn k : ℕ} → IsNat b nb → IsNat n nn →
    Nat.log nb nn = k → IsNat (Nat.log b n) k
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Given the natural number literal `ex`, returns its square root as a natural number literal
and an equality proof. Panics if `ex` isn't a natural number literal. -/
def proveNatLog (eb en : Q(ℕ)) : (ek : Q(ℕ)) × Q(Nat.log $eb $en = $ek) :=
  match eb.natLit!, en.natLit! with
  -- TODO: special cases for small values
  -- | 0 => show (ey : Q(ℕ)) × Q(Nat.sqrt 0 = $ey) from ⟨mkRawNatLit 0, q(Nat.sqrt_zero)⟩
  -- | 1 => show (ey : Q(ℕ)) × Q(Nat.sqrt 1 = $ey) from ⟨mkRawNatLit 1, q(Nat.sqrt_one)⟩
  | b, n =>
    let k := Nat.log b n
    have ek : Q(ℕ) := mkRawNatLit k
    have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
    have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true):= (q(Eq.refl true) : Expr)
    ⟨ek, q(nat_log_helper $eb $en $ek $hl $hh)⟩

/-- Evaluates the `Nat.log` function. -/
@[norm_num Nat.log _ _]
def evalNatLog : NormNumExt where eval {u α} e := do
  let mkApp2 _ (b : Q(ℕ)) (n : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  let ⟨ek, pf⟩ := proveNatLog eb en
  let pf' : Q(IsNat (Nat.log $b $n) $ek) := q(isNat_log $pb $pn $pf)
  return .isNat sℕ ek pf'

end NormNum

end Tactic
