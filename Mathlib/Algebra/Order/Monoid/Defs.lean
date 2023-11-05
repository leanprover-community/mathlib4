/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Lemmas
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

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
class OrderedAddCommMonoid (α : Type*) extends AddCommMonoid α, PartialOrder α where
  /-- Addition is monotone in an `OrderedAddCommMonoid`. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

attribute [to_additive] OrderedCommMonoid

section OrderedInstances

@[to_additive]
instance OrderedCommMonoid.to_covariantClass_left (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedCommMonoid.mul_le_mul_left _ _ bc a

/- This instance can be proven with `by infer_instance`.  However, `WithBot ℕ` does not
pick up a `CovariantClass M M (function.swap (*)) (≤)` instance without it (see PR mathlib#7940). -/
@[to_additive]
instance OrderedCommMonoid.to_covariantClass_right (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_of_covariant_mul M _

#noalign has_mul.to_covariant_class_left
#noalign has_add.to_covariant_class_left
#noalign has_mul.to_covariant_class_right
#noalign has_add.to_covariant_class_right

end OrderedInstances

set_option linter.deprecated false in
@[deprecated] theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos' h h

/-- A linearly ordered additive commutative monoid. -/
class LinearOrderedAddCommMonoid (α : Type*) extends LinearOrder α, OrderedAddCommMonoid α

/-- A linearly ordered commutative monoid. -/
@[to_additive]
class LinearOrderedCommMonoid (α : Type*) extends LinearOrder α, OrderedCommMonoid α

attribute [to_additive existing] LinearOrderedCommMonoid.toOrderedCommMonoid

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    Top α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is larger than any other element.-/
  protected le_top : ∀ x : α, x ≤ ⊤
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedCommMonoid α] {a : α}

@[to_additive, simp]
theorem one_le_mul_self_iff : 1 ≤ a * a ↔ 1 ≤ a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_lt_one' h h).mtr, fun h ↦ one_le_mul h h⟩

@[to_additive, simp]
theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[to_additive, simp]
theorem mul_self_le_one_iff : a * a ≤ 1 ↔ a ≤ 1 := by simp [← not_iff_not]

@[to_additive, simp]
theorem mul_self_lt_one_iff : a * a < 1 ↔ a < 1 := by simp [← not_iff_not]
