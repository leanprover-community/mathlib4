/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Basic

/-! # The order relation on the integers -/

open Nat

namespace Int

#align int.nonneg Int.NonNeg
#align int.le Int.le
#align int.lt Int.lt

export private decNonneg from Init.Data.Int.Basic
#align int.decidable_nonneg Int.decNonneg
#align int.decidable_le Int.decLe
#align int.decidable_lt Int.decLt

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'
#align int.le.elim Int.le.elim

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le
#align int.coe_nat_le_coe_nat_of_le Int.ofNat_le_ofNat_of_le
#align int.le_of_coe_nat_le_coe_nat Int.le_of_ofNat_le_ofNat
#align int.coe_nat_le_coe_nat_iff Int.ofNat_le

#align int.coe_zero_le Int.ofNat_zero_le
#align int.eq_coe_of_zero_le Int.eq_ofNat_of_zero_le

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'
#align int.lt.elim Int.lt.elim

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt
#align int.coe_nat_lt_coe_nat_iff Int.ofNat_lt
#align int.lt_of_coe_nat_lt_coe_nat Int.lt_of_ofNat_lt_ofNat
#align int.coe_nat_lt_coe_nat_of_lt Int.ofNat_lt_ofNat_of_lt

instance instLinearOrderInt : LinearOrder ℤ where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidableEq := by infer_instance
                    -- 🎉 no goals
                    -- 🎉 no goals
  decidableLE := by infer_instance
  decidableLT := by infer_instance
                    -- 🎉 no goals

#align int.eq_nat_abs_of_zero_le Int.eq_natAbs_of_zero_le
#align int.le_nat_abs Int.le_natAbs
#align int.eq_neg_succ_of_lt_zero Int.eq_negSucc_of_lt_zero
#align int.sub_eq_zero_iff_eq Int.sub_eq_zero

theorem neg_mul_eq_neg_mul_symm (a b : ℤ) : -a * b = -(a * b) := (Int.neg_mul_eq_neg_mul a b).symm
#align int.neg_mul_eq_neg_mul_symm Int.neg_mul_eq_neg_mul_symm

theorem mul_neg_eq_neg_mul_symm (a b : ℤ) : a * -b = -(a * b) := (Int.neg_mul_eq_mul_neg a b).symm
#align int.mul_neg_eq_neg_mul_symm Int.mul_neg_eq_neg_mul_symm

#align int.of_nat_nonneg Int.ofNat_nonneg
#align int.coe_succ_pos Int.ofNat_succ_pos
#align int.exists_eq_neg_of_nat Int.exists_eq_neg_ofNat
#align int.nat_abs_of_nonneg Int.natAbs_of_nonneg
#align int.of_nat_nat_abs_of_nonpos Int.ofNat_natAbs_of_nonpos

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match lt_trichotomy 0 a with
  | Or.inl hlt₁ =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 < a * b := Int.mul_pos hlt₁ hlt₂
      -- ⊢ a = 0 ∨ b = 0
      rw [h] at this
      -- ⊢ a = 0 ∨ b = 0
      exact absurd this (lt_irrefl _)
      -- 🎉 no goals
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 > a * b := Int.mul_neg_of_pos_of_neg hlt₁ hgt₂
      -- ⊢ a = 0 ∨ b = 0
      rw [h] at this
      -- ⊢ a = 0 ∨ b = 0
      exact absurd this (lt_irrefl _)
      -- 🎉 no goals
  | Or.inr (Or.inl heq₁) => Or.inl heq₁.symm
  | Or.inr (Or.inr hgt₁) =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 > a * b := Int.mul_neg_of_neg_of_pos hgt₁ hlt₂
      -- ⊢ a = 0 ∨ b = 0
      rw [h] at this
      -- ⊢ a = 0 ∨ b = 0
      exact absurd this (lt_irrefl _)
      -- 🎉 no goals
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 < a * b := Int.mul_pos_of_neg_of_neg hgt₁ hgt₂
      -- ⊢ a = 0 ∨ b = 0
      rw [h] at this
      -- ⊢ a = 0 ∨ b = 0
      exact absurd this (lt_irrefl _)
      -- 🎉 no goals
#align int.eq_zero_or_eq_zero_of_mul_eq_zero Int.eq_zero_or_eq_zero_of_mul_eq_zero
