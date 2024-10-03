/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Defs

/-!
# Theory of Idempotent Semigroups and Monoids

An idempotent semigroup is a semigroup that satisfies `x * x = x`.

## Main definitions

* class `AddIdemSemigroup`: an additive semigroup satisfying `x + x = x`.

* class `IdemSemigroup`: a semigroup satisfying `x * x = x`.

* class `AddMonoid`: an additive monoid satisfying `x + x = x`.

* class `IdemMonoid`: a monoid satisfying `x * x = x`.

## Naming conventions

## Notation

## References

## TODO

-/

/-- An idempotent additive semigroup is a type with an associative idempotent `(+)`. -/
class AddIdemSemigroup (G : Type _) extends AddSemigroup G where
  protected add_idem : ∀ x : G, x + x = x

/-- An idempotent semigroup is a type with an associative idempotent `(*)`. -/
@[to_additive]
class IdemSemigroup (G : Type _) extends Semigroup G where
  protected mul_idem : ∀ x : G, x * x = x

section IdemSemigroup

variable (G : Type _)
variable [IdemSemigroup G]

/-- Making mul_idem available globally -/
@[to_additive]
theorem mul_idem (x : G) : x * x = x := IdemSemigroup.mul_idem _

end IdemSemigroup

/-- An idempotent additive monoid is an additive monoid and an idempotent semigroup. -/
class AddIdemMonoid (G : Type _) extends AddMonoid G, AddIdemSemigroup G

/-- An idempotent additive monoid is an additive monoid and an idempotent semigroup. -/
@[to_additive]
class IdemMonoid (G : Type _) extends Monoid G, IdemSemigroup G
