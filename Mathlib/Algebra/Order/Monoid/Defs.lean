/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.BoundedOrder

#align_import algebra.order.monoid.defs from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/


open Function

variable {α β : Type*}

/-- An ordered (additive) commutative monoid is a commutative monoid with a partial order such that
addition is monotone. -/
class OrderedAddCommMonoid (α : Type*) extends AddCommMonoid α, PartialOrder α where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
#align ordered_add_comm_monoid OrderedAddCommMonoid

/-- An ordered commutative monoid is a commutative monoid with a partial order such that
multiplication is monotone. -/
@[to_additive]
class OrderedCommMonoid (α : Type*) extends CommMonoid α, PartialOrder α where
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b
#align ordered_comm_monoid OrderedCommMonoid

section OrderedCommMonoid
variable [OrderedCommMonoid α]

@[to_additive]
instance OrderedCommMonoid.toCovariantClassLeft : CovariantClass α α (· * ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedCommMonoid.mul_le_mul_left _ _ bc a
#align ordered_comm_monoid.to_covariant_class_left OrderedCommMonoid.toCovariantClassLeft
#align ordered_add_comm_monoid.to_covariant_class_left OrderedAddCommMonoid.toCovariantClassLeft

/- This instance can be proven with `by infer_instance`.  However, `WithBot ℕ` does not
pick up a `CovariantClass M M (Function.swap (*)) (≤)` instance without it (see PR mathlib#7940). -/
@[to_additive]
instance OrderedCommMonoid.toCovariantClassRight (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_of_covariant_mul M _
#align ordered_comm_monoid.to_covariant_class_right OrderedCommMonoid.toCovariantClassRight
#align ordered_add_comm_monoid.to_covariant_class_right OrderedAddCommMonoid.toCovariantClassRight

end OrderedCommMonoid

/-- An ordered cancellative additive commutative monoid is a partially ordered commutative additive
monoid in which addition is cancellative and monotone. -/
class OrderedCancelAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α where
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
#align ordered_cancel_add_comm_monoid OrderedCancelAddCommMonoid

/-- An ordered cancellative commutative monoid is a partially ordered commutative monoid in which
multiplication is cancellative and monotone. -/
@[to_additive OrderedCancelAddCommMonoid]
class OrderedCancelCommMonoid (α : Type*) extends OrderedCommMonoid α where
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
#align ordered_cancel_comm_monoid OrderedCancelCommMonoid

#align ordered_cancel_comm_monoid.to_ordered_comm_monoid OrderedCancelCommMonoid.toOrderedCommMonoid
#align ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid OrderedCancelAddCommMonoid.toOrderedAddCommMonoid

section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.toContravariantClassLeLeft :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩
#align ordered_cancel_comm_monoid.to_contravariant_class_le_left OrderedCancelCommMonoid.toContravariantClassLeLeft
#align ordered_cancel_add_comm_monoid.to_contravariant_class_le_left OrderedCancelAddCommMonoid.toContravariantClassLeLeft

#noalign ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left
#noalign ordered_cancel_add_comm_monoid.lt_of_add_lt_add_left

@[to_additive]
instance OrderedCancelCommMonoid.toContravariantClassLeft :
    ContravariantClass α α (· * ·) (· < ·) where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim
#align ordered_cancel_comm_monoid.to_contravariant_class_left OrderedCancelCommMonoid.toContravariantClassLeft
#align ordered_cancel_add_comm_monoid.to_contravariant_class_left OrderedCancelAddCommMonoid.toContravariantClassLeft

/- This instance can be proven with `by infer_instance`.  However, by analogy with the
instance `OrderedCancelCommMonoid.to_covariantClass_right` above, I imagine that without
this instance, some Type would not have a `ContravariantClass M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.toContravariantClassRight :
    ContravariantClass α α (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_of_contravariant_mul α _
#align ordered_cancel_comm_monoid.to_contravariant_class_right OrderedCancelCommMonoid.toContravariantClassRight
#align ordered_cancel_add_comm_monoid.to_contravariant_class_right OrderedCancelAddCommMonoid.toContravariantClassRight

-- See note [lower instance priority]
@[to_additive OrderedCancelAddCommMonoid.toCancelAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel :=
      fun a b c h => (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }
#align ordered_cancel_comm_monoid.to_cancel_comm_monoid OrderedCancelCommMonoid.toCancelCommMonoid
#align ordered_cancel_add_comm_monoid.to_cancel_add_comm_monoid OrderedCancelAddCommMonoid.toCancelAddCommMonoid

#noalign has_mul.to_covariant_class_left
#noalign has_add.to_covariant_class_left
#noalign has_mul.to_covariant_class_right
#noalign has_add.to_covariant_class_right

end OrderedCancelCommMonoid

set_option linter.deprecated false in
@[deprecated (since := "2022-11-28")]
theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a := add_pos' h h
#align bit0_pos bit0_pos

/-- A linearly ordered additive commutative monoid. -/
class LinearOrderedAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α, LinearOrder α
#align linear_ordered_add_comm_monoid LinearOrderedAddCommMonoid

/-- A linearly ordered commutative monoid. -/
@[to_additive]
class LinearOrderedCommMonoid (α : Type*) extends OrderedCommMonoid α, LinearOrder α
#align linear_ordered_comm_monoid LinearOrderedCommMonoid

/-- A linearly ordered cancellative additive commutative monoid is an additive commutative monoid
with a decidable linear order in which addition is cancellative and monotone. -/
class LinearOrderedCancelAddCommMonoid (α : Type*) extends OrderedCancelAddCommMonoid α,
    LinearOrderedAddCommMonoid α
#align linear_ordered_cancel_add_comm_monoid LinearOrderedCancelAddCommMonoid

/-- A linearly ordered cancellative commutative monoid is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[to_additive LinearOrderedCancelAddCommMonoid]
class LinearOrderedCancelCommMonoid (α : Type*) extends OrderedCancelCommMonoid α,
    LinearOrderedCommMonoid α
#align linear_ordered_cancel_comm_monoid LinearOrderedCancelCommMonoid

attribute [to_additive existing] LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
#align linear_ordered_add_comm_monoid_with_top LinearOrderedAddCommMonoidWithTop
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

variable [LinearOrderedCommMonoid α] {a : α}

@[to_additive (attr := simp)]
theorem one_le_mul_self_iff : 1 ≤ a * a ↔ 1 ≤ a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_lt_one' h h).mtr, fun h ↦ one_le_mul h h⟩

@[to_additive (attr := simp)]
theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[to_additive (attr := simp)]
theorem mul_self_le_one_iff : a * a ≤ 1 ↔ a ≤ 1 := by simp [← not_iff_not]

@[to_additive (attr := simp)]
theorem mul_self_lt_one_iff : a * a < 1 ↔ a < 1 := by simp [← not_iff_not]
