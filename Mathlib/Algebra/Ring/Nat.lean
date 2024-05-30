/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Ring.Defs

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

/-!
# The natural numbers form a semiring

This file contains the commutative semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

open Multiplicative

namespace Nat

/-! ### Instances -/

instance instCommSemiring : CommSemiring ℕ where
  __ := instCommMonoid
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl
  natCast n := n
  natCast_zero := rfl
  natCast_succ _ := rfl

instance instCancelCommMonoidWithZero : CancelCommMonoidWithZero ℕ where
  __ : CommMonoidWithZero ℕ := by infer_instance
  mul_left_cancel_of_ne_zero h := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
#align nat.cancel_comm_monoid_with_zero Nat.instCancelCommMonoidWithZero

instance instMulDivCancelClass : MulDivCancelClass ℕ where
  mul_div_cancel _ _b hb := Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)

instance instCharZero : CharZero ℕ where cast_injective := Function.injective_id

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instAddCommMonoidWithOne : AddCommMonoidWithOne ℕ := by infer_instance
instance instDistrib              : Distrib ℕ              := by infer_instance
instance instSemiring             : Semiring ℕ             := by infer_instance

end Nat
