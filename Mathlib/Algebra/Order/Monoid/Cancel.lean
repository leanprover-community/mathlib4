/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Defs


/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/



/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
class OrderedCancelAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  /-- Addition is monotone in an ordered cancellative additive commutative monoid. -/
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  /-- Additive cancellation is compatible with the order in an ordered cancellative additive
    commutative monoid. -/
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[to_additive OrderedCancelAddCommMonoid]
class OrderedCancelCommMonoid (α : Type u) extends CommMonoid α, PartialOrder α where
  /-- Multiplication is monotone in an ordered cancellative commutative monoid. -/
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  /-- Cancellation is compatible with the order in an ordered cancellative commutative monoid. -/
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c


-- see Note [lower instance priority]
@[to_additive OrderedCancelAddCommMonoid.toOrderedAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid [OrderedCancelCommMonoid α] :
    OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }
