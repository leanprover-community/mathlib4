/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.PNat.Algebra
public import Mathlib.Data.PNat.Order

/-!
# Ordered algebraic lemmas for positive natural numbers
-/

@[expose] public section

deriving instance IsOrderedCancelMonoid for PNat

namespace PNat

open Nat

instance instCancelCommMonoid : CancelCommMonoid ℕ+ where

@[simp]
theorem one_add_natPred (n : ℕ+) : 1 + n.natPred = n := by
  rw [natPred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]

@[simp]
theorem natPred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_natPred

theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2

theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)

theorem add_one (a : ℕ+) : a + 1 = succPNat a := rfl

theorem lt_succ_self (a : ℕ+) : a < succPNat a := Nat.lt_add_one a

/- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance instSub : Sub ℕ+ :=
  ⟨fun a b => toPNat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (toPNat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl

theorem sub_le (a b : ℕ+) : a - b ≤ a := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

theorem le_sub_one_of_lt {a b : ℕ+} (hab : a < b) : a ≤ b - (1 : ℕ+) := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
  fun h =>
    PNat.eq <| by
      rw [add_coe, sub_coe, ite_eq_left h]
      exact add_tsub_cancel_of_le h.le

theorem sub_add_of_lt {a b : ℕ+} (h : b < a) : a - b + b = a := by
  rw [add_comm, add_sub_of_lt h]

@[simp]
theorem add_sub {a b : ℕ+} : a + b - b = a :=
  add_right_cancel (sub_add_of_lt (lt_add_left _ _))

end PNat
