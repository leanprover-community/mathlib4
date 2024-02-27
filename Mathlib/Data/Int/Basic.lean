/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Monotone.Basic

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Basic algebraic instances on the integers

This file contains instances on `ℤ`. The stronger one is `Int.linearOrderedCommRing`.
-/

set_option autoImplicit true

open Nat

namespace Int

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

lemma cast_Nat_cast [AddGroupWithOne R] : (Int.cast (Nat.cast n) : R) = Nat.cast n :=
  Int.cast_ofNat _

@[simp, norm_cast] lemma cast_pow [Ring R] (n : ℤ) (m : ℕ) : ↑(n ^ m) = (n ^ m : R) := by
  induction' m with m ih <;> simp [_root_.pow_succ, *]
#align int.cast_pow Int.cast_pow

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

lemma natAbs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction' k with k ih
  · rfl
  · rw [_root_.pow_succ, natAbs_mul, Nat.pow_succ, ih, Nat.mul_comm]
#align int.nat_abs_pow Int.natAbs_pow

theorem coe_nat_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2
#align int.coe_nat_strict_mono Int.coe_nat_strictMono

section Multiplicative

open Multiplicative

lemma toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align int.to_add_pow Int.toAdd_pow

lemma toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align int.to_add_zpow Int.toAdd_zpow

@[simp] lemma ofAdd_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_zpow ..).symm
#align int.of_add_mul Int.ofAdd_mul

end Multiplicative

end Int

-- TODO: Do we really need this lemma? This is just `smul_eq_mul`
lemma zsmul_int_int (a b : ℤ) : a • b = a * b := rfl
#align zsmul_int_int zsmul_int_int

lemma zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := mul_one _
#align zsmul_int_one zsmul_int_one

assert_not_exists Set.range
