/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Order.Monotone.Basic

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Basic operations on the integers

This file contains:
* instances on `ℤ`. The stronger one is `Int.linearOrderedCommRing`.
* some basic lemmas about integers
-/

set_option autoImplicit true

open Nat

namespace Int

instance instNontrivialInt : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

instance instCommRingInt : CommRing ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := by rw [Int.mul_comm]; rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = x + n * x
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [ofNat_eq_coe, ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [negSucc_coe, ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

@[simp, norm_cast] lemma cast_id : Int.cast n = n := rfl

@[simp, norm_cast]
theorem cast_mul [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp] lemma ofNat_eq_cast : Int.ofNat n = n := rfl

lemma cast_Nat_cast [AddGroupWithOne R] : (Int.cast (Nat.cast n) : R) = Nat.cast n :=
  Int.cast_ofNat _

@[norm_cast]
lemma cast_eq_cast_iff_Nat (m n : ℕ) : (m : ℤ) = (n : ℤ) ↔ m = n := ofNat_inj

@[simp, norm_cast]
lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

@[to_additive (attr := simp, norm_cast) coe_nat_zsmul]
theorem _root_.zpow_coe_nat [DivInvMonoid G] (a : G) (n : ℕ) : a ^ (Nat.cast n : ℤ) = a ^ n :=
  zpow_ofNat ..
#align coe_nat_zsmul coe_nat_zsmul

/-! ### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/
instance : AddCommMonoid ℤ    := by infer_instance
instance : AddMonoid ℤ        := by infer_instance
instance : Monoid ℤ           := by infer_instance
instance : CommMonoid ℤ       := by infer_instance
instance : CommSemigroup ℤ    := by infer_instance
instance : Semigroup ℤ        := by infer_instance
instance : AddCommGroup ℤ     := by infer_instance
instance : AddGroup ℤ         := by infer_instance
instance : AddCommSemigroup ℤ := by infer_instance
instance : AddSemigroup ℤ     := by infer_instance
instance : CommSemiring ℤ     := by infer_instance
instance : Semiring ℤ         := by infer_instance
instance instRingInt : Ring ℤ             := by infer_instance
instance : Distrib ℤ          := by infer_instance

#align int.neg_succ_not_nonneg Int.negSucc_not_nonneg
#align int.neg_succ_not_pos Int.negSucc_not_pos
#align int.neg_succ_sub_one Int.negSucc_sub_one
#align int.coe_nat_mul_neg_succ Int.ofNat_mul_negSucc
#align int.neg_succ_mul_coe_nat Int.negSucc_mul_ofNat
#align int.neg_succ_mul_neg_succ Int.negSucc_mul_negSucc

#align int.coe_nat_le Int.ofNat_le
#align int.coe_nat_lt Int.ofNat_lt

theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n := Int.ofNat_inj
#align int.coe_nat_inj' Int.coe_nat_inj'

theorem coe_nat_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2
#align int.coe_nat_strict_mono Int.coe_nat_strictMono

theorem coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := ofNat_le.2 (Nat.zero_le _)
#align int.coe_nat_nonneg Int.coe_nat_nonneg

#align int.neg_of_nat_ne_zero Int.negSucc_ne_zero
#align int.zero_ne_neg_of_nat Int.zero_ne_negSucc

@[simp]
theorem sign_coe_add_one (n : ℕ) : Int.sign (n + 1) = 1 :=
  rfl
#align int.sign_coe_add_one Int.sign_coe_add_one

@[simp]
theorem sign_negSucc (n : ℕ) : Int.sign -[n+1] = -1 :=
  rfl
#align int.sign_neg_succ_of_nat Int.sign_negSucc

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1
#align int.succ Int.succ

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1
#align int.pred Int.pred

theorem nat_succ_eq_int_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n := rfl
#align int.nat_succ_eq_int_succ Int.nat_succ_eq_int_succ

theorem pred_succ (a : ℤ) : pred (succ a) = a := add_sub_cancel _ _
#align int.pred_succ Int.pred_succ

theorem succ_pred (a : ℤ) : succ (pred a) = a := sub_add_cancel _ _
#align int.succ_pred Int.succ_pred

theorem neg_succ (a : ℤ) : -succ a = pred (-a) := neg_add _ _
#align int.neg_succ Int.neg_succ

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]
#align int.succ_neg_succ Int.succ_neg_succ

theorem neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [neg_eq_iff_eq_neg.mp (neg_succ (-a)), neg_neg]
#align int.neg_pred Int.neg_pred

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]
#align int.pred_neg_pred Int.pred_neg_pred

theorem pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n
#align int.pred_nat_succ Int.pred_nat_succ

theorem neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n
#align int.neg_nat_succ Int.neg_nat_succ

theorem succ_neg_nat_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n
#align int.succ_neg_nat_succ Int.succ_neg_nat_succ

@[norm_cast] theorem coe_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp
#align int.coe_pred_of_pos Int.coe_pred_of_pos

@[elab_as_elim] protected theorem induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  induction i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz, Nat.cast_zero]
    | succ n ih => convert hn _ ih using 1; simp [sub_eq_neg_add]
#align int.induction_on Int.induction_on

/-! ### nat abs -/

theorem natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩
#align int.nat_abs_surjective Int.natAbs_surjective

#align int.nat_abs_add_le Int.natAbs_add_le
#align int.nat_abs_sub_le Int.natAbs_sub_le
#align int.nat_abs_neg_of_nat Int.natAbs_negOfNat
#align int.nat_abs_mul Int.natAbs_mul
#align int.nat_abs_mul_nat_abs_eq Int.natAbs_mul_natAbs_eq
#align int.nat_abs_mul_self' Int.natAbs_mul_self'
#align int.neg_succ_of_nat_eq' Int.negSucc_eq'

@[deprecated natAbs_ne_zero]
theorem natAbs_ne_zero_of_ne_zero : ∀ {a : ℤ}, a ≠ 0 → natAbs a ≠ 0 := natAbs_ne_zero.2
#align int.nat_abs_ne_zero_of_ne_zero Int.natAbs_ne_zero_of_ne_zero

#align int.nat_abs_eq_zero Int.natAbs_eq_zero
#align int.nat_abs_ne_zero Int.natAbs_ne_zero
#align int.nat_abs_lt_nat_abs_of_nonneg_of_lt Int.natAbs_lt_natAbs_of_nonneg_of_lt
#align int.nat_abs_eq_nat_abs_iff Int.natAbs_eq_natAbs_iff
#align int.nat_abs_eq_iff Int.natAbs_eq_iff

/-! ### `/`  -/

-- Porting note: Many of the theorems in this section are dubious alignments because the default
-- division on `Int` has changed from the E-rounding convention to the T-rounding convention
-- (see `Int.ediv`). We have attempted to align the theorems to continue to use the `/` symbol
-- where possible, but some theorems fail to hold on T-rounding division and have been aligned to
-- `Int.ediv` instead.

#align int.of_nat_div Int.ofNat_div

@[simp, norm_cast] theorem coe_nat_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl
#align int.coe_nat_div Int.coe_nat_div

theorem coe_nat_ediv (m n : ℕ) : ((m / n : ℕ) : ℤ) = ediv m n := rfl

#align int.neg_succ_of_nat_div Int.negSucc_ediv

#align int.div_neg Int.div_negₓ -- int div alignment

theorem ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [add_sub_cancel]; rfl
#align int.div_of_neg_of_pos Int.ediv_of_neg_of_pos

#align int.div_nonneg Int.div_nonnegₓ -- int div alignment
#align int.div_neg' Int.ediv_neg'
#align int.div_one Int.div_oneₓ -- int div alignment
#align int.div_eq_zero_of_lt Int.div_eq_zero_of_ltₓ -- int div alignment

/-! ### mod -/

#align int.of_nat_mod Int.ofNat_mod_ofNat

@[simp, norm_cast] theorem coe_nat_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl
#align int.coe_nat_mod Int.coe_nat_mod

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

theorem sign_coe_nat_of_nonzero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 := sign_ofNat_of_nonzero hn
#align int.sign_coe_nat_of_nonzero Int.sign_coe_nat_of_nonzero

#align int.div_sign Int.div_sign -- int div alignment
#align int.of_nat_add_neg_succ_of_nat_of_lt Int.ofNat_add_negSucc_of_lt
#align int.neg_add_neg Int.negSucc_add_negSucc

/-! ### toNat -/

#align int.to_nat_eq_max Int.toNat_eq_max
#align int.to_nat_zero Int.toNat_zero
#align int.to_nat_one Int.toNat_one
#align int.to_nat_of_nonneg Int.toNat_of_nonneg

@[simp] theorem toNat_coe_nat (n : ℕ) : toNat ↑n = n := rfl
#align int.to_nat_coe_nat Int.toNat_coe_nat

@[simp] theorem toNat_coe_nat_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 := rfl
#align int.to_nat_coe_nat_add_one Int.toNat_coe_nat_add_one

#align int.le_to_nat Int.self_le_toNat
#align int.le_to_nat_iff Int.le_toNat
#align int.to_nat_add Int.toNat_add
#align int.to_nat_add_nat Int.toNat_add_nat
#align int.pred_to_nat Int.pred_toNat
#align int.to_nat_sub_to_nat_neg Int.toNat_sub_toNat_neg
#align int.to_nat_add_to_nat_neg_eq_nat_abs Int.toNat_add_toNat_neg_eq_natAbs
#align int.mem_to_nat' Int.mem_toNat'
#align int.to_nat_neg_nat Int.toNat_neg_nat
