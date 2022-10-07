/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Monoid
import Mathlib.Algebra.Order.Group


/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`semiring`, `comm_semiring`, `ring`, `comm_ring`)
* an order class (`partial_order`, `linear_order`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `ordered_semiring`: Semiring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_semiring`: Commutative semiring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `ordered_ring`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_ring`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_semiring`: Semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_comm_semiring`: Commutative semiring with a linear order such that `+` respects
  `≤` and `*` respects `<`.
* `linear_ordered_ring`: Ring with a linear order such that `+` respects `≤` and `*` respects `<`.
* `linear_ordered_comm_ring`: Commutative ring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `canonically_ordered_comm_semiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

and some typeclasses to define ordered rings by specifying their nonegative elements:
* `nonneg_ring`: To define `ordered_ring`s.
* `linear_nonneg_ring`: To define `linear_ordered_ring`s.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `ordered_semiring`
  - `ordered_cancel_add_comm_monoid` & multiplication & `*` respects `<`
  - `semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_semiring`
  - `ordered_semiring` & commutativity of multiplication
  - `comm_semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_ring`
  - `ordered_semiring` & additive inverses
  - `ordered_add_comm_group` & multiplication & `*` respects `<`
  - `ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_ring`
  - `ordered_ring` & commutativity of multiplication
  - `ordered_comm_semiring` & additive inverses
  - `comm_ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `linear_ordered_semiring`
  - `ordered_semiring` & totality of the order & nontriviality
* `linear_ordered_comm_semiring`
  - `ordered_comm_semiring` & totality of the order & nontriviality
  - `linear_ordered_semiring` & commutativity of multiplication
  - `linear_ordered_add_comm_monoid` & multiplication & nontriviality & `*` respects `<`
* `linear_ordered_ring`
  - `ordered_ring` & totality of the order & nontriviality
  - `linear_ordered_semiring` & additive inverses
  - `linear_ordered_add_comm_group` & multiplication & `*` respects `<`
  - `domain` & linear order structure
* `linear_ordered_comm_ring`
  - `ordered_comm_ring` & totality of the order & nontriviality
  - `linear_ordered_ring` & commutativity of multiplication
  - `linear_ordered_comm_semiring` & additive inverses
  - `is_domain` & linear order structure
* `canonically_ordered_comm_semiring`
  - `canonically_ordered_add_monoid` & multiplication & `*` respects `<` & no zero divisors
  - `comm_semiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `canonically_ordered_semiring`
They have yet to come up in practice.
-/

/-- An `OrderedSemiring α` is a semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α where
  zero_le_one : (0 : α) ≤ 1
  mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

/-- An `OrderedRing α` is a ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  zero_le_one : 0 ≤ (1 : α)
  mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

section OrderedRing

variable [OrderedRing α] {a b c : α}

theorem OrderedRing.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact OrderedRing.mul_pos _ _ h₂ (sub_pos.2 h₁)

theorem OrderedRing.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  rw [← sub_pos, ← sub_mul]
  exact OrderedRing.mul_pos _ _ (sub_pos.2 h₁) h₂

-- see Note [lower instance priority]
instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
  { ‹OrderedRing α›, Ring.toSemiring with
    le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
    mul_lt_mul_of_pos_left := @OrderedRing.mul_lt_mul_of_pos_left α _,
    mul_lt_mul_of_pos_right := @OrderedRing.mul_lt_mul_of_pos_right α _ }

theorem mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := neg_pos_of_neg hc
  have : b * -c < a * -c := mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by rwa [mul_neg, mul_neg] at this
  lt_of_neg_lt_neg this

theorem mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := mul_lt_mul_of_neg_right ha hb
  rwa [zero_mul] at this

end OrderedRing
