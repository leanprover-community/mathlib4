/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Ring.GrindInstances

/-!
# The integers are a ring

This file contains the commutative ring instance on `ℤ`.

See note [foundational algebra order theory].
-/

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

instance instCommRing : CommRing ℤ where
  __ := instAddCommGroup
  __ := instCommSemigroup
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance instCancelCommMonoidWithZero : CancelCommMonoidWithZero ℤ where
  mul_left_cancel_of_ne_zero ha _ _ := (mul_eq_mul_left_iff ha).1

instance instIsDomain : IsDomain ℤ where

instance instCharZero : CharZero ℤ where cast_injective _ _ := ofNat.inj

instance instMulDivCancelClass : MulDivCancelClass ℤ where mul_div_cancel _ _ := mul_ediv_cancel _

@[simp, norm_cast]
lemma cast_mul {α : Type*} [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) :=
  fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]

@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : ℤ) (m : ℕ) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction m <;> simp [_root_.pow_succ, *]

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

set_option linter.style.commandStart false

instance instCommSemiring : CommSemiring ℤ := inferInstance
instance instSemiring     : Semiring ℤ     := inferInstance
instance instRing         : Ring ℤ         := inferInstance
instance instDistrib      : Distrib ℤ      := inferInstance

set_option linter.style.commandStart true

end Int
