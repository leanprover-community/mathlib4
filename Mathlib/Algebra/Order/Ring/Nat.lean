/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear ordered semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

@[expose] public section

namespace Nat

/-! ### Instances -/

instance instIsStrictOrderedRing : IsStrictOrderedRing ℕ where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha

instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ where
  bot := 0
  bot_le := zero_le
  zero_le_one := zero_le_one
  mul_le_mul_left _ _ h c := Nat.mul_le_mul_right c h

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, ← not_even_iff_odd]

end Nat
