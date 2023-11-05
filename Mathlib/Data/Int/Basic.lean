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



theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n := Int.ofNat_inj

theorem coe_nat_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

theorem coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := ofNat_le.2 (Nat.zero_le _)


@[simp]
theorem sign_coe_add_one (n : ℕ) : Int.sign (n + 1) = 1 :=
  rfl

@[simp]
theorem sign_negSucc (n : ℕ) : Int.sign -[n+1] = -1 :=
  rfl

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

theorem nat_succ_eq_int_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n := rfl

theorem pred_succ (a : ℤ) : pred (succ a) = a := add_sub_cancel _ _

theorem succ_pred (a : ℤ) : succ (pred a) = a := sub_add_cancel _ _

theorem neg_succ (a : ℤ) : -succ a = pred (-a) := neg_add _ _

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [neg_eq_iff_eq_neg.mp (neg_succ (-a)), neg_neg]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n

theorem neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n

theorem succ_neg_nat_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n

@[norm_cast] theorem coe_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp

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

/-! ### nat abs -/

theorem natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩


@[deprecated natAbs_ne_zero]
theorem natAbs_ne_zero_of_ne_zero : ∀ {a : ℤ}, a ≠ 0 → natAbs a ≠ 0 := natAbs_ne_zero.2


/-! ### `/`  -/

-- Porting note: Many of the theorems in this section are dubious alignments because the default
-- division on `Int` has changed from the E-rounding convention to the T-rounding convention
-- (see `Int.ediv`). We have attempted to align the theorems to continue to use the `/` symbol
-- where possible, but some theorems fail to hold on T-rounding division and have been aligned to
-- `Int.ediv` instead.


@[simp, norm_cast] theorem coe_nat_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl

theorem coe_nat_ediv (m n : ℕ) : ((m / n : ℕ) : ℤ) = ediv m n := rfl



theorem ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [add_sub_cancel]; rfl


/-! ### mod -/


@[simp, norm_cast] theorem coe_nat_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl


/-! ### properties of `/` and `%` -/



theorem sign_coe_nat_of_nonzero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 := sign_ofNat_of_nonzero hn


/-! ### toNat -/


@[simp] theorem toNat_coe_nat (n : ℕ) : toNat ↑n = n := rfl

@[simp] theorem toNat_coe_nat_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 := rfl
