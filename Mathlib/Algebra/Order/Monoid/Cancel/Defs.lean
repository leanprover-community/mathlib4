/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Defs

#align_import algebra.order.monoid.cancel.defs from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Ordered cancellative monoids
-/


universe u

variable {α : Type u}

open Function

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
class OrderedCancelAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  /-- Addition is monotone in an ordered cancellative additive commutative monoid. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  /-- Additive cancellation is compatible with the order in an ordered cancellative additive
    commutative monoid. -/
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
#align ordered_cancel_add_comm_monoid OrderedCancelAddCommMonoid

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
class OrderedCancelCommMonoid (α : Type u) extends CommMonoid α, PartialOrder α where
  /-- Multiplication is monotone in an ordered cancellative commutative monoid. -/
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  /-- Cancellation is compatible with the order in an ordered cancellative commutative monoid. -/
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
#align ordered_cancel_comm_monoid OrderedCancelCommMonoid

attribute [to_additive OrderedCancelAddCommMonoid] OrderedCancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.to_contravariantClass_le_left :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩
#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.to_contravariantClass_le_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_le_left OrderedCancelAddCommMonoid.to_contravariantClass_le_left

@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
  fun a b c h =>
  lt_of_le_not_le (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)
#align ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left OrderedCancelCommMonoid.lt_of_mul_lt_mul_left
#align ordered_cancel_add_comm_monoid.lt_of_add_lt_add_left OrderedCancelAddCommMonoid.lt_of_add_lt_add_left

@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_left (M : Type*)
    [OrderedCancelCommMonoid M] :
    ContravariantClass M M (· * ·) (· < ·) where
  elim _ _ _ := OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _
#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.to_contravariantClass_left
#align ordered_cancel_add_comm_monoid.to_contravariant_class_left OrderedCancelAddCommMonoid.to_contravariantClass_left

/- This instance can be proven with `by infer_instance`.  However, by analogy with the
instance `OrderedCancelCommMonoid.to_covariantClass_right` above, I imagine that without
this instance, some Type would not have a `ContravariantClass M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariantClass_right (M : Type*)
    [OrderedCancelCommMonoid M] :
    ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M
#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.to_contravariantClass_right
#align ordered_cancel_add_comm_monoid.to_contravariant_class_right OrderedCancelAddCommMonoid.to_contravariantClass_right

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }
#align ordered_cancel_comm_monoid.to_ordered_comm_monoid OrderedCancelCommMonoid.toOrderedCommMonoid
#align ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid OrderedCancelAddCommMonoid.toOrderedAddCommMonoid

-- see Note [lower instance priority]
@[to_additive OrderedCancelAddCommMonoid.toCancelAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel :=
      fun a b c h => (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }
#align ordered_cancel_comm_monoid.to_cancel_comm_monoid OrderedCancelCommMonoid.toCancelCommMonoid
#align ordered_cancel_add_comm_monoid.to_cancel_add_comm_monoid OrderedCancelAddCommMonoid.toCancelAddCommMonoid

end OrderedCancelCommMonoid

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
class LinearOrderedCancelAddCommMonoid (α : Type u) extends OrderedCancelAddCommMonoid α,
    LinearOrderedAddCommMonoid α
#align linear_ordered_cancel_add_comm_monoid LinearOrderedCancelAddCommMonoid

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
class LinearOrderedCancelCommMonoid (α : Type u) extends OrderedCancelCommMonoid α,
    LinearOrderedCommMonoid α
#align linear_ordered_cancel_comm_monoid LinearOrderedCancelCommMonoid

attribute [to_additive LinearOrderedCancelAddCommMonoid] LinearOrderedCancelCommMonoid
attribute [to_additive existing] LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid
