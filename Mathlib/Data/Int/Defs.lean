/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Convert

#align_import init.data.int.comp_lemmas from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

## TODO

Split this file into:
* `Data.Int.Init` (or maybe `Data.Int.Batteries`?) for lemmas that could go to Batteries
* `Data.Int.Basic` for the lemmas that require mathlib definitions
-/

open Nat

namespace Int
variable {m n : ℕ}

#noalign int.ne_neg_of_ne
#noalign int.neg_ne_zero_of_ne
#noalign int.zero_ne_neg_of_ne
#noalign int.neg_ne_of_pos
#noalign int.ne_neg_of_pos
#noalign int.bit0_nonneg
#noalign int.bit1_nonneg
#noalign int.nonneg_of_pos
#noalign int.ne_of_nat_abs_ne_nat_abs_of_nonneg
#noalign int.ne_of_nat_ne_nonneg_case
#noalign int.nat_abs_bit0
#noalign int.nat_abs_bit0_step
#noalign int.nat_abs_bit1_nonneg
#noalign int.nat_abs_bit1_nonneg_step
#align int.neg_succ_lt_zero Int.negSucc_lt_zero
#align int.of_nat_nat_abs_eq_of_nonneg Int.ofNat_natAbs_eq_of_nonnegₓ
#align int.nat_abs_of_neg_succ_of_nat Int.natAbs_negSucc

-- TODO: Tag in Lean
attribute [simp] natAbs_pos

protected lemma one_pos : 0 < (1 : Int) := Int.zero_lt_one
#align int.one_pos Int.one_pos

protected lemma one_nonneg : 0 ≤ (1 : ℤ) := Int.le_of_lt Int.zero_lt_one
#align int.one_nonneg Int.one_nonneg

lemma zero_le_ofNat (n : ℕ) : 0 ≤ ofNat n := @le.intro _ _ n (by rw [Int.zero_add]; rfl)
#align int.zero_le_of_nat Int.zero_le_ofNat

instance instNontrivial : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

@[simp] lemma ofNat_eq_natCast : Int.ofNat n = n := rfl

@[deprecated ofNat_eq_natCast] -- 2024-03-24
protected lemma natCast_eq_ofNat (n : ℕ) : ↑n = Int.ofNat n := rfl
#align int.coe_nat_eq Int.natCast_eq_ofNat

@[norm_cast] lemma natCast_inj : (m : ℤ) = (n : ℤ) ↔ m = n := ofNat_inj
#align int.coe_nat_inj' Int.natCast_inj

@[simp, norm_cast] lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma natCast_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

lemma natCast_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 := by omega
#align int.coe_nat_eq_zero Int.natCast_eq_zero

lemma natCast_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by omega
#align int.coe_nat_ne_zero Int.natCast_ne_zero

lemma natCast_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n := by omega
#align int.coe_nat_ne_zero_iff_pos Int.natCast_ne_zero_iff_pos

#align int.neg_succ_not_nonneg Int.negSucc_not_nonneg
#align int.neg_succ_not_pos Int.negSucc_not_pos
#align int.neg_succ_sub_one Int.negSucc_sub_one
#align int.coe_nat_mul_neg_succ Int.ofNat_mul_negSucc
#align int.neg_succ_mul_coe_nat Int.negSucc_mul_ofNat
#align int.neg_succ_mul_neg_succ Int.negSucc_mul_negSucc

#align int.coe_nat_le Int.ofNat_le
#align int.coe_nat_lt Int.ofNat_lt

lemma natCast_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := ofNat_le.2 (Nat.zero_le _)
#align int.coe_nat_nonneg Int.natCast_nonneg

#align int.neg_of_nat_ne_zero Int.negSucc_ne_zero
#align int.zero_ne_neg_of_nat Int.zero_ne_negSucc

@[simp] lemma sign_natCast_add_one (n : ℕ) : sign (n + 1) = 1 := rfl
#align int.sign_coe_add_one Int.sign_natCast_add_one

#align int.sign_neg_succ_of_nat Int.sign_negSucc

protected lemma two_mul : ∀ n : ℤ, 2 * n = n + n
  | (n : ℕ) => by norm_cast; exact n.two_mul
  | -[n+1] => by
    change (2 : ℕ) * (_ : ℤ) = _
    rw [Int.ofNat_mul_negSucc, Nat.two_mul, ofNat_add, Int.neg_add]
    rfl

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated] lemma ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := rfl
#align int.coe_nat_bit0 Int.ofNat_bit0

@[norm_cast, deprecated] lemma ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := rfl
#align int.coe_nat_bit1 Int.ofNat_bit1

end deprecated

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1
#align int.succ Int.succ

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1
#align int.pred Int.pred

lemma natCast_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n := rfl
#align int.nat_succ_eq_int_succ Int.natCast_succ

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _
#align int.pred_succ Int.pred_succ

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _
#align int.succ_pred Int.succ_pred

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add
#align int.neg_succ Int.neg_succ

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]
#align int.succ_neg_succ Int.succ_neg_succ

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]
#align int.neg_pred Int.neg_pred

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]
#align int.pred_neg_pred Int.pred_neg_pred

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n
#align int.pred_nat_succ Int.pred_nat_succ

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n
#align int.neg_nat_succ Int.neg_nat_succ

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n
#align int.succ_neg_nat_succ Int.succ_neg_natCast_succ

@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp [ofNat_succ]
#align int.coe_pred_of_pos Int.natCast_pred_of_pos

@[elab_as_elim] protected lemma induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  induction i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz]
    | succ n ih => convert hn _ ih using 1; simp [ofNat_succ, Int.neg_add, Int.sub_eq_add_neg]
#align int.induction_on Int.induction_on

/-! ### nat abs -/

-- TODO: Rename `natAbs_of_Nat` to `natAbs_natCast`
lemma natAbs_ofNat' (n : ℕ) : natAbs (ofNat n) = n := rfl
#align int.nat_abs_of_nat_core Int.natAbs_ofNat'

lemma natAbs_add_of_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → natAbs (a + b) = natAbs a + natAbs b
  | ofNat _, ofNat _, _, _ => rfl
#align int.nat_abs_add_nonneg Int.natAbs_add_of_nonneg

lemma natAbs_add_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs (a + b) = natAbs a + natAbs b := by
  omega
#align int.nat_abs_add_neg Int.natAbs_add_of_nonpos

lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩
#align int.nat_abs_surjective Int.natAbs_surjective

#align int.nat_abs_add_le Int.natAbs_add_le
#align int.nat_abs_sub_le Int.natAbs_sub_le
#align int.nat_abs_neg_of_nat Int.natAbs_negOfNat
#align int.nat_abs_mul Int.natAbs_mul
#align int.nat_abs_mul_nat_abs_eq Int.natAbs_mul_natAbs_eq
#align int.nat_abs_mul_self' Int.natAbs_mul_self'
#align int.neg_succ_of_nat_eq' Int.negSucc_eq'

@[deprecated natAbs_ne_zero]
lemma natAbs_ne_zero_of_ne_zero : ∀ {a : ℤ}, a ≠ 0 → natAbs a ≠ 0 := natAbs_ne_zero.2
#align int.nat_abs_ne_zero_of_ne_zero Int.natAbs_ne_zero_of_ne_zero

#align int.nat_abs_eq_zero Int.natAbs_eq_zero
#align int.nat_abs_ne_zero Int.natAbs_ne_zero
#align int.nat_abs_lt_nat_abs_of_nonneg_of_lt Int.natAbs_lt_natAbs_of_nonneg_of_lt
#align int.nat_abs_eq_nat_abs_iff Int.natAbs_eq_natAbs_iff
#align int.nat_abs_eq_iff Int.natAbs_eq_iff

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by
  simp [Int.pow_succ, Int.pow_zero, Int.natAbs_mul_self']
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

/-! ### `/`  -/

-- Porting note: Many of the lemmas in this section are dubious alignments because the default
-- division on `Int` has changed from the E-rounding convention to the T-rounding convention
-- (see `Int.ediv`). We have attempted to align the lemmas to continue to use the `/` symbol
-- where possible, but some lemmas fail to hold on T-rounding division and have been aligned to
-- `Int.ediv` instead.

#align int.of_nat_div Int.ofNat_div

@[simp, norm_cast] lemma natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl
#align int.coe_nat_div Int.natCast_div

lemma natCast_ediv (m n : ℕ) : ((m / n : ℕ) : ℤ) = ediv m n := rfl

#align int.neg_succ_of_nat_div Int.negSucc_ediv

#align int.div_neg Int.div_negₓ -- int div alignment

lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl
#align int.div_of_neg_of_pos Int.ediv_of_neg_of_pos

#align int.div_nonneg Int.div_nonnegₓ -- int div alignment
#align int.div_neg' Int.ediv_neg'
#align int.div_one Int.div_oneₓ -- int div alignment
#align int.div_eq_zero_of_lt Int.div_eq_zero_of_ltₓ -- int div alignment

/-! ### mod -/

#align int.of_nat_mod Int.ofNat_mod_ofNat

@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl
#align int.coe_nat_mod Int.natCast_mod

#align int.neg_succ_of_nat_mod Int.negSucc_emod
#align int.mod_neg Int.mod_negₓ -- int div alignment
#align int.zero_mod Int.zero_modₓ -- int div alignment
#align int.mod_zero Int.mod_zeroₓ -- int div alignment
#align int.mod_one Int.mod_oneₓ -- int div alignment
#align int.mod_eq_of_lt Int.emod_eq_of_lt -- int div alignment
#align int.mod_add_div Int.emod_add_ediv -- int div alignment
#align int.div_add_mod Int.div_add_modₓ -- int div alignment
#align int.mod_add_div' Int.mod_add_div'ₓ -- int div alignment
#align int.div_add_mod' Int.div_add_mod'ₓ -- int div alignment
#align int.mod_def Int.mod_defₓ -- int div alignment

/-! ### properties of `/` and `%` -/

#align int.mul_div_mul_of_pos Int.mul_ediv_mul_of_pos
#align int.mul_div_mul_of_pos_left Int.mul_ediv_mul_of_pos_left
#align int.mul_mod_mul_of_pos Int.mul_emod_mul_of_pos
#align int.mul_div_cancel_of_mod_eq_zero Int.mul_div_cancel_of_mod_eq_zeroₓ -- int div alignment
#align int.div_mul_cancel_of_mod_eq_zero Int.div_mul_cancel_of_mod_eq_zeroₓ -- int div alignment

#align int.nat_abs_sign Int.natAbs_sign
#align int.nat_abs_sign_of_nonzero Int.natAbs_sign_of_nonzero

lemma sign_natCast_of_ne_zero (hn : n ≠ 0) : Int.sign n = 1 := sign_ofNat_of_nonzero hn
#align int.sign_coe_nat_of_nonzero Int.sign_natCast_of_ne_zero

#align int.div_sign Int.div_sign -- int div alignment
#align int.of_nat_add_neg_succ_of_nat_of_lt Int.ofNat_add_negSucc_of_lt
#align int.neg_add_neg Int.negSucc_add_negSucc

/-! ### toNat -/

#align int.to_nat_eq_max Int.toNat_eq_max
#align int.to_nat_zero Int.toNat_zero
#align int.to_nat_one Int.toNat_one
#align int.to_nat_of_nonneg Int.toNat_of_nonneg

@[simp] lemma toNat_natCast (n : ℕ) : toNat ↑n = n := rfl
#align int.to_nat_coe_nat Int.toNat_natCast

@[simp] lemma toNat_natCast_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 := rfl
#align int.to_nat_coe_nat_add_one Int.toNat_natCast_add_one

#align int.le_to_nat Int.self_le_toNat
#align int.le_to_nat_iff Int.le_toNat
#align int.to_nat_add Int.toNat_add
#align int.to_nat_add_nat Int.toNat_add_nat
#align int.pred_to_nat Int.pred_toNat
#align int.to_nat_sub_to_nat_neg Int.toNat_sub_toNat_neg
#align int.to_nat_add_to_nat_neg_eq_nat_abs Int.toNat_add_toNat_neg_eq_natAbs
#align int.mem_to_nat' Int.mem_toNat'
#align int.to_nat_neg_nat Int.toNat_neg_nat

-- Porting note: this was added in an ad hoc port for use in `Tactic/NormNum/Basic`
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl

-- 2024-04-02
@[deprecated] alias ofNat_eq_cast := ofNat_eq_natCast
@[deprecated] alias cast_eq_cast_iff_Nat := natCast_inj
@[deprecated] alias coe_nat_sub := Int.natCast_sub
@[deprecated] alias coe_nat_nonneg := natCast_nonneg
@[deprecated] alias sign_coe_add_one := sign_natCast_add_one
@[deprecated] alias nat_succ_eq_int_succ := natCast_succ
@[deprecated] alias succ_neg_nat_succ := succ_neg_natCast_succ
@[deprecated] alias coe_pred_of_pos := natCast_pred_of_pos
@[deprecated] alias coe_nat_div := natCast_div
@[deprecated] alias coe_nat_ediv := natCast_ediv
@[deprecated] alias sign_coe_nat_of_nonzero := sign_natCast_of_ne_zero
@[deprecated] alias toNat_coe_nat := toNat_natCast
@[deprecated] alias toNat_coe_nat_add_one := toNat_natCast_add_one
