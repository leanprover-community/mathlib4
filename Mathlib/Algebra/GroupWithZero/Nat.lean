/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Tactic.Spread

/-!
# The natural numbers form a cancellative `CommMonoidWithZero`

This file contains the `CommMonoidWithZero` and `IsCancelMulZero` instances on the natural numbers.

See note [foundational algebra order theory].
-/

@[expose] public section

assert_not_exists Ring

namespace Nat

instance instMulZeroClass : MulZeroClass ℕ where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

instance instSemigroupWithZero : SemigroupWithZero ℕ where
  __ := instSemigroup
  __ := instMulZeroClass

instance instMonoidWithZero : MonoidWithZero ℕ where
  __ := instMonoid
  __ := instMulZeroClass
  __ := instSemigroupWithZero

instance instCommMonoidWithZero : CommMonoidWithZero ℕ where
  __ := instCommMonoid
  __ := instMonoidWithZero

instance instIsCancelMulZero : IsCancelMulZero ℕ where
  mul_left_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
  mul_right_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h)

instance instMulDivCancelClass : MulDivCancelClass ℕ where
  mul_div_cancel _ _b hb := Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)

instance instMulZeroOneClass : MulZeroOneClass ℕ where
  __ := instMulZeroClass
  __ := instMulOneClass

end Nat
