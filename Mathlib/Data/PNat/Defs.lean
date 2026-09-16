/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.PNat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe
public import Mathlib.Tactic.Lift

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `Data.PNat.Basic`, as they need more imports.
-/

@[expose] public section

deriving instance LinearOrder for PNat

namespace PNat
/- Predecessor of a `ℕ+`, as a `ℕ`. -/
def natPred (i : ℕ+) : ℕ :=
  i - 1

@[simp]
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl

end PNat

namespace Nat

/- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩

/- Write a successor as an element of `ℕ+`. -/
def succPNat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
theorem succPNat_coe (n : ℕ) : (succPNat n : ℕ) = succ n :=
  rfl

@[simp]
theorem natPred_succPNat (n : ℕ) : n.succPNat.natPred = n :=
  rfl

@[simp]
theorem _root_.PNat.succPNat_natPred (n : ℕ+) : n.natPred.succPNat = n :=
  Subtype.ext <| succ_pred_eq_of_pos n.2

/- Convert a natural number to a `PNat`. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPNat' (n : ℕ) : ℕ+ :=
  succPNat (pred n)

@[simp]
theorem toPNat'_zero : Nat.toPNat' 0 = 1 := rfl

@[simp]
theorem toPNat'_coe : ∀ n : ℕ, (toPNat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [ite_eq_left (succ_pos m)]
    rfl

end Nat

namespace PNat

open Nat

theorem toPNat'_coe {n : ℕ} : 0 < n → (n.toPNat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
theorem coe_toPNat' (n : ℕ+) : (n : ℕ).toPNat' = n :=
  eq (toPNat'_coe n.pos)

end PNat

section CanLift

instance Nat.canLiftPNat : CanLift ℕ ℕ+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩

instance Int.canLiftPNat : CanLift ℤ ℕ+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe, ite_eq_left (Int.natAbs_pos.2 hn.ne'),
        Int.natAbs_of_nonneg hn.le]⟩⟩

end CanLift
