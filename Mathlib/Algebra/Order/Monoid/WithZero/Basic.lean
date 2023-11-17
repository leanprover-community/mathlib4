/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.WithZero.Defs
import Mathlib.Algebra.GroupWithZero.Basic

#align_import algebra.order.monoid.with_zero.basic from "leanprover-community/mathlib"@"dad7ecf9a1feae63e6e49f07619b7087403fb8d4"

/-!
# An instance orphaned from `Algebra.Order.Monoid.WithZero.Defs`

We put this here to minimise imports: if you can move it back into
`Algebra.Order.Monoid.WithZero.Defs` without increasing imports, please do.
-/


open Function

universe u

variable {α : Type u}

namespace WithZero

instance contravariantClass_mul_lt [Mul α] [PartialOrder α]
    [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) := by
  refine ⟨fun a b c h => ?_⟩
  have := ((zero_le _).trans_lt h).ne'
  induction a using WithZero.recZeroCoe
  · exfalso; exact left_ne_zero_of_mul this rfl
  induction c using WithZero.recZeroCoe
  · exfalso; exact right_ne_zero_of_mul this rfl
  induction b using WithZero.recZeroCoe
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]
#align with_zero.contravariant_class_mul_lt WithZero.contravariantClass_mul_lt

end WithZero
