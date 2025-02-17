/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Util.AssertExists

/-!
# Ordered groups

This file defines bundled ordered groups and develops a few basic results.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

/-
`NeZero` theory should not be needed at this point in the ordered algebraic hierarchy.
-/
assert_not_imported Mathlib.Algebra.NeZero

open Function

universe u

variable {α : Type u}

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  /-- Addition is monotone in an ordered additive commutative group. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

/-- An ordered commutative group is a commutative group
with a partial order in which multiplication is strictly monotone. -/
class OrderedCommGroup (α : Type u) extends CommGroup α, PartialOrder α where
  /-- Multiplication is monotone in an ordered commutative group. -/
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

attribute [to_additive] OrderedCommGroup

@[to_additive]
instance OrderedCommGroup.toMulLeftMono (α : Type u) [OrderedCommGroup α] :
    MulLeftMono α where
      elim a b c bc := OrderedCommGroup.mul_le_mul_left b c bc a

-- See note [lower instance priority]
@[to_additive OrderedAddCommGroup.toOrderedCancelAddCommMonoid]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
{ ‹OrderedCommGroup α› with le_of_mul_le_mul_left := fun _ _ _ ↦ le_of_mul_le_mul_left' }

example (α : Type u) [OrderedAddCommGroup α] : AddRightStrictMono α :=
  inferInstance

-- Porting note: this instance is not used,
-- and causes timeouts after https://github.com/leanprover/lean4/pull/2210.
-- It was introduced in https://github.com/leanprover-community/mathlib/pull/17564
-- but without the motivation clearly explained.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.toMulLeftReflectLE (α : Type u) [OrderedCommGroup α] :
    MulLeftReflectLE α where
      elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹

-- Porting note: this instance is not used,
-- and causes timeouts after https://github.com/leanprover/lean4/pull/2210.
-- See further explanation on `OrderedCommGroup.toMulLeftReflectLE`.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.toMulRightReflectLE (α : Type u) [OrderedCommGroup α] :
    MulRightReflectLE α where
      elim a b c bc := by simpa using mul_le_mul_right' bc a⁻¹

alias OrderedCommGroup.mul_lt_mul_left' := mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'

alias OrderedCommGroup.le_of_mul_le_mul_left := le_of_mul_le_mul_left'

attribute [to_additive] OrderedCommGroup.le_of_mul_le_mul_left

alias OrderedCommGroup.lt_of_mul_lt_mul_left := lt_of_mul_lt_mul_left'

attribute [to_additive] OrderedCommGroup.lt_of_mul_lt_mul_left


/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[to_additive]
class LinearOrderedCommGroup (α : Type u) extends OrderedCommGroup α, LinearOrder α

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {a : α}

@[to_additive LinearOrderedAddCommGroup.add_lt_add_left]
theorem LinearOrderedCommGroup.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
  _root_.mul_lt_mul_left' h c

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
    [LinearOrderedCommGroup α] : LinearOrderedCancelCommMonoid α :=
{ ‹LinearOrderedCommGroup α›, OrderedCommGroup.toOrderedCancelCommMonoid with }

end LinearOrderedCommGroup
