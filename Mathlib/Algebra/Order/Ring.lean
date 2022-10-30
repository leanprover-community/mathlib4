/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Monoid
import Mathlib.Algebra.Order.Group
import Mathlib.Logic.Nontrivial


/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`semiring`, `comm_semiring`, `ring`, `comm_ring`)
* an order class (`partial_order`, `linear_order`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `ordered_semiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `strict_ordered_semiring`: Semiring with a partial order such that `+` and `*` respects `<`.
* `ordered_comm_semiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `strict_ordered_comm_semiring`: Commutative semiring with a partial order such that `+` and `*`
  respect `<`.
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

and some typeclasses to define ordered rings by specifying their nonnegative elements:
* `nonneg_ring`: To define `ordered_ring`s.
* `linear_nonneg_ring`: To define `linear_ordered_ring`s.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `ordered_semiring`
  - `ordered_add_comm_monoid` & multiplication & `*` respects `≤`
  - `semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `strict_ordered_semiring`
  - `ordered_cancel_add_comm_monoid` & multiplication & `*` respects `<`
  - `ordered_semiring` & `+` respects `<` & `*` respects `<`
* `ordered_comm_semiring`
  - `ordered_semiring` & commutativity of multiplication
  - `comm_semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `strict_ordered_comm_semiring`
  - `strict_ordered_semiring` & commutativity of multiplication
  - `ordered_comm_semiring` & `+` respects `<` & `*` respects `<`
* `ordered_ring`
  - `strict_ordered_semiring` & additive inverses
  - `ordered_add_comm_group` & multiplication & `*` respects `<`
  - `ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_ring`
  - `ordered_ring` & commutativity of multiplication
  - `ordered_comm_semiring` & additive inverses
  - `comm_ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `linear_ordered_semiring`
  - `strict_ordered_semiring` & totality of the order & nontriviality
  - `linear_ordered_add_comm_monoid` & multiplication & nontriviality & `*` respects `<`
* `linear_ordered_comm_semiring`
  - `strict_ordered_comm_semiring` & totality of the order & nontriviality
  - `linear_ordered_semiring` & commutativity of multiplication
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
  - `canonically_ordered_add_monoid` & multiplication & `*` respects `≤` & no zero divisors
  - `comm_semiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `canonically_ordered_semiring`
They have yet to come up in practice.
-/

/-- An `OrderedSemiring α` is a semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α where
  /-- `0 ≤ 1` in any ordered semiring. -/
  zero_le_one : (0 : α) ≤ 1
  /-- In an ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- In an ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

/-- An `OrderedRing α` is a ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  /-- `0 ≤ 1` in any ordered ring. -/
  zero_le_one : 0 ≤ (1 : α)
  /-- The product of positive elements is positive. -/
  mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

-- TODO These are necessary because of https://github.com/leanprover/lean4/issues/1730
attribute [nolint docBlame] OrderedSemiring.le_of_add_le_add_left
attribute [nolint docBlame] OrderedSemiring.add_le_add_left
attribute [nolint docBlame] OrderedRing.add_le_add_left

/-- An `ordered_comm_semiring` is a commutative semiring with a partial order such that addition is
monotone and multiplication by a nonnegative number is monotone. -/
class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α

/-- An `ordered_comm_ring` is a commutative ring with a partial order such that addition is monotone
and multiplication by a nonnegative number is monotone. -/
class OrderedCommRing (α : Type u) extends OrderedRing α, CommRing α

/-- A `strict_ordered_semiring` is a semiring with a partial order such that addition is strictly
monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α where
  /-- In a strict ordered semiring, `0 ≤ 1`. -/
  zero_le_one : (0 : α) ≤ 1
  /-- Left multiplication by a positive element is strictly monotone. -/
  mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  /-- Right multiplication by a positive element is strictly monotone. -/
  mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

/-- A `strict_ordered_comm_semiring` is a commutative semiring with a partial order such that
addition is strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommSemiring (α : Type u) extends StrictOrderedSemiring α, CommSemiring α

/-- A `strict_ordered_ring` is a ring with a partial order such that addition is strictly monotone
and multiplication by a positive number is strictly monotone. -/
class StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

/-- A `strict_ordered_comm_ring` is a commutative ring with a partial order such that addition is
strictly monotone and multiplication by a positive number is strictly monotone. -/
class StrictOrderedCommRing (α : Type _) extends StrictOrderedRing α, CommRing α

/- It's not entirely clear we should assume `nontrivial` at this point; it would be reasonable to
explore changing this, but be warned that the instances involving `domain` may cause typeclass
search loops. -/
/-- A `linear_ordered_semiring` is a nontrivial semiring with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedSemiring (α : Type u) extends StrictOrderedSemiring α, LinearOrderedAddCommMonoid α, Nontrivial α

/-- A `linear_ordered_comm_semiring` is a nontrivial commutative semiring with a linear order such
that addition is monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommSemiring (α : Type _) extends StrictOrderedCommSemiring α, LinearOrderedSemiring α

/-- A `linear_ordered_ring` is a ring with a linear order such that addition is monotone and
multiplication by a positive number is strictly monotone. -/
class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α, Nontrivial α

/-- A `linear_ordered_comm_ring` is a commutative ring with a linear order such that addition is
monotone and multiplication by a positive number is strictly monotone. -/
class LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α, CommMonoid α
