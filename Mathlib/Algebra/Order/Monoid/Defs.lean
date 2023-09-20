/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.BoundedOrder

#align_import algebra.order.monoid.defs from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/


open Function

universe u

variable {α : Type u} {β : Type*}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
class OrderedCommMonoid (α : Type*) extends CommMonoid α, PartialOrder α where
  /-- Multiplication is monotone in an `OrderedCommMonoid`. -/
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
#align ordered_comm_monoid OrderedCommMonoid

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
class OrderedAddCommMonoid (α : Type*) extends AddCommMonoid α, PartialOrder α where
  /-- Addition is monotone in an `OrderedAddCommMonoid`. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
#align ordered_add_comm_monoid OrderedAddCommMonoid

attribute [to_additive] OrderedCommMonoid

/-- An ordered (additive) commutative monoid *with one* is an additive commutative monoid with one
with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone) and `0 ≤ 1`. -/
class OrderedAddCommMonoidWithOne (α : Type*) extends AddCommMonoidWithOne α, PartialOrder α where
  /-- Addition is monotone in an `OrderedAddCommMonoidWithOne`. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  /-- One is nonnegative in an `OrderedAddCommMonoidWithOne`. -/
  protected zero_le_one : (0 : α) ≤ 1

section OrderedInstances

-- See note [lower instance priority]
instance (priority := 100) OrderedAddCommMonoidWithOne.toOrderedAddCommMonoid {M : Type*}
    [OrderedAddCommMonoidWithOne M] : OrderedAddCommMonoid M where
  add_le_add_left := OrderedAddCommMonoidWithOne.add_le_add_left

-- see Note [lower instance priority]
instance (priority := 100) OrderedAddCommMonoidWithOne.zeroLEOneClass {M : Type*}
    [OrderedAddCommMonoidWithOne M] : ZeroLEOneClass M where
  zero_le_one := OrderedAddCommMonoidWithOne.zero_le_one

@[to_additive]
instance OrderedCommMonoid.to_covariantClass_left (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedCommMonoid.mul_le_mul_left _ _ bc a
#align ordered_comm_monoid.to_covariant_class_left OrderedCommMonoid.to_covariantClass_left
#align ordered_add_comm_monoid.to_covariant_class_left OrderedAddCommMonoid.to_covariantClass_left

/- This instance can be proven with `by infer_instance`.  However, `WithBot ℕ` does not
pick up a `CovariantClass M M (function.swap (*)) (≤)` instance without it (see PR mathlib#7940). -/
@[to_additive]
instance OrderedCommMonoid.to_covariantClass_right (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_of_covariant_mul M _
#align ordered_comm_monoid.to_covariant_class_right OrderedCommMonoid.to_covariantClass_right
#align ordered_add_comm_monoid.to_covariant_class_right OrderedAddCommMonoid.to_covariantClass_right

#noalign has_mul.to_covariant_class_left
#noalign has_add.to_covariant_class_left
#noalign has_mul.to_covariant_class_right
#noalign has_add.to_covariant_class_right

end OrderedInstances

set_option linter.deprecated false in
@[deprecated] theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos' h h
#align bit0_pos bit0_pos

/-- A linearly ordered additive commutative monoid. -/
class LinearOrderedAddCommMonoid (α : Type*) extends LinearOrder α, OrderedAddCommMonoid α
#align linear_ordered_add_comm_monoid LinearOrderedAddCommMonoid

/-- A linearly ordered commutative monoid. -/
@[to_additive]
class LinearOrderedCommMonoid (α : Type*) extends LinearOrder α, OrderedCommMonoid α
#align linear_ordered_comm_monoid LinearOrderedCommMonoid

attribute [to_additive existing] LinearOrderedCommMonoid.toOrderedCommMonoid

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    Top α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is larger than any other element.-/
  protected le_top : ∀ x : α, x ≤ ⊤
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
#align linear_ordered_add_comm_monoid_with_top LinearOrderedAddCommMonoidWithTop

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }
#align linear_ordered_add_comm_monoid_with_top.to_order_top LinearOrderedAddCommMonoidWithTop.toOrderTop

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a
#align top_add top_add

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)
#align add_top add_top

end LinearOrderedAddCommMonoidWithTop
