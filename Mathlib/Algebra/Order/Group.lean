/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.MonoidLemmas

/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

open Function

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

section Group
variable [Group α] [LT α]

section TypeclassesLeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/-- Uses `Left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff "Uses `Left` co(ntra)variant."]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

end TypeclassesLeftLt

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

-- FIXME: restore @[to_additive sub_pos]
@[simp]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

end Right

end Group

alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv
