/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Set.Basic

#align_import data.nat.order.basic from "leanprover-community/mathlib"@"3ed3f98a1e836241990d3d308f1577e434977130"

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear orderded semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

namespace Nat

/-! ### Instances -/

instance instLinearOrderedCommSemiring : LinearOrderedCommSemiring ℕ where
  __ := instCommSemiring
  __ := instLinearOrder
  add_le_add_left := @Nat.add_le_add_left
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left
  zero_le_one := Nat.le_of_lt (Nat.zero_lt_succ 0)
  mul_lt_mul_of_pos_left := @Nat.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := @Nat.mul_lt_mul_of_pos_right
  exists_pair_ne := ⟨0, 1, ne_of_lt Nat.zero_lt_one⟩

instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ where
  __ := instLinearOrderedCommSemiring
  __ : CommMonoidWithZero ℕ := inferInstance
  mul_le_mul_left _ _ h c := Nat.mul_le_mul_left c h

instance instCanonicallyOrderedCommSemiring : CanonicallyOrderedCommSemiring ℕ where
  __ := instLinearOrderedCommSemiring
  exists_add_of_le h := (Nat.le.dest h).imp fun _ => Eq.symm
  le_self_add := Nat.le_add_right
  eq_zero_or_eq_zero_of_mul_eq_zero := Nat.eq_zero_of_mul_eq_zero

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instLinearOrderedSemiring : LinearOrderedSemiring ℕ := inferInstance
instance instStrictOrderedSemiring : StrictOrderedSemiring ℕ := inferInstance
instance instStrictOrderedCommSemiring : StrictOrderedCommSemiring ℕ := inferInstance
instance instOrderedSemiring : OrderedSemiring ℕ := StrictOrderedSemiring.toOrderedSemiring'
instance instOrderedCommSemiring : OrderedCommSemiring ℕ :=
  StrictOrderedCommSemiring.toOrderedCommSemiring'

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, odd_iff_not_even]
#align nat.is_compl_even_odd Nat.isCompl_even_odd

end Nat
