/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.LinearOrder
import Mathlib.Init
import Mathlib.Logic.Basic

/-!
# The order relation on the integers
-/

@[expose] public section

open Nat

namespace Int

variable {a b : ℤ}

theorem le.elim (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

theorem lt.elim (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

instance instLinearOrder : LinearOrder ℤ where
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt_iff_le_not_ge := @Int.lt_iff_le_and_not_ge
  le_total := Int.le_total
  toDecidableEq := instDecidableEq
  toDecidableLE := decLe
  toDecidableLT := decLt

protected alias ⟨eq_zero_or_eq_zero_of_mul_eq_zero, _⟩ := Int.mul_eq_zero

theorem nonneg_or_nonpos_of_mul_nonneg : 0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  grind [Int.mul_comm, Int.mul_nonneg_iff_of_pos_right]

theorem mul_nonneg_of_nonneg_or_nonpos : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 → 0 ≤ a * b
  | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb
  | .inr ⟨ha, hb⟩ => Int.mul_nonneg_of_nonpos_of_nonpos ha hb

protected theorem mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩

protected theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rw [Int.lt_iff_le_and_ne, Int.mul_nonneg_iff, ne_comm, Int.mul_ne_zero_iff]
  lia

protected theorem mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← not_iff_not, not_le, Int.mul_pos_iff]
  lia

protected theorem mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← not_iff_not, not_lt, Int.mul_nonneg_iff]
  lia

end Int
