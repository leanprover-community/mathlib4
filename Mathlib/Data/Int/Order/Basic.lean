/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Order.Defs.LinearOrder

/-!
# The order relation on the integers
-/

open Nat

namespace Int

export private decNonneg from Init.Data.Int.Basic

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

instance instLinearOrder : LinearOrder ℤ where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidableEq := by infer_instance
  decidableLE := by infer_instance
  decidableLT := by infer_instance

@[deprecated (since := "2024-07-27")] alias mul_neg_eq_neg_mul_symm := Int.mul_neg
@[deprecated (since := "2024-07-27")] alias neg_mul_eq_neg_mul_symm := Int.neg_mul

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  Int.mul_eq_zero.mp h

theorem nonneg_or_nonpos_of_mul_nonneg {a b : ℤ} : 0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  intro h
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · exact .inl ⟨ha, hb⟩
  · refine .inr ⟨?_, le_of_not_le hb⟩
    obtain _ | _ := Int.mul_eq_zero.mp <|
      Int.le_antisymm (Int.mul_nonpos_of_nonneg_of_nonpos ha <| le_of_not_le hb) h
    all_goals omega
  · refine .inr ⟨le_of_not_le ha, ?_⟩
    obtain _ | _ := Int.mul_eq_zero.mp <|
      Int.le_antisymm (Int.mul_nonpos_of_nonpos_of_nonneg (le_of_not_le ha) hb) h
    all_goals omega
  · exact .inr ⟨le_of_not_ge ha, le_of_not_ge hb⟩

theorem mul_nonneg_of_nonneg_or_nonpos {a b : ℤ} : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 → 0 ≤ a * b
  | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb
  | .inr ⟨ha, hb⟩ => Int.mul_nonneg_of_nonpos_of_nonpos ha hb

protected theorem mul_nonneg_iff {a b : ℤ} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩
end Int
