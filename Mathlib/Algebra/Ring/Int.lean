/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Units
import Mathlib.Data.Int.Cast.Basic

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"
#align_import data.int.units from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# The integers are a ring

This file contains the commutative ring instance on `ℤ`.

See note [foundational algebra order theory].
-/

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
  mul_left_cancel_of_ne_zero {_a _b _c} ha := (mul_eq_mul_left_iff ha).1

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
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : ℤ) (m : ℕ) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction' m with m ih <;> simp [_root_.pow_succ, *]
#align int.cast_pow Int.cast_pow

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

instance instCommSemiring : CommSemiring ℤ := inferInstance
instance instSemiring     : Semiring ℤ     := inferInstance
instance instRing         : Ring ℤ         := inferInstance
instance instDistrib      : Distrib ℤ      := inferInstance

/-! ### Miscellaneous lemmas -/

/-! #### Units -/

lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using isUnit_eq_one_or u.isUnit
#align int.units_eq_one_or Int.units_eq_one_or

lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using isUnit_ne_iff_eq_neg u.isUnit v.isUnit

end Int

assert_not_exists Set.range
