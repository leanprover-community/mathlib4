/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Monoid
import Mathlib.Algebra.Ring.Defs

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Basic algebraic instances on the integers

This file contains the `CommRing ℤ` instance.
-/

open Nat

namespace Int

instance instCommRingInt : CommRing ℤ where
  __ := instAddCommGroupWithOneInt
  __ := instCommSemigroupInt
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl

@[simp, norm_cast]
theorem cast_mul {α : Type*} [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : ℤ) (m : ℕ) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction' m with m ih <;> simp [_root_.pow_succ, *]
#align int.cast_pow Int.cast_pow

/-! ### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/
instance : CommSemiring ℤ     := by infer_instance
instance : Semiring ℤ         := by infer_instance
instance instRingInt : Ring ℤ             := by infer_instance
instance : Distrib ℤ          := by infer_instance

end Int

assert_not_exists Set.range
