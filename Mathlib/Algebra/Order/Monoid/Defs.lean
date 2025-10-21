/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/


open Function

variable {α : Type*}

-- TODO: assume weaker typeclasses

/-- An ordered (additive) monoid is a monoid with a partial order such that addition is monotone. -/
class IsOrderedAddMonoid (α : Type*) [AddCommMonoid α] [PartialOrder α] where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
  protected add_le_add_right : ∀ a b : α, a ≤ b → ∀ c, a + c ≤ b + c := fun a b h c ↦ by
    rw [add_comm _ c, add_comm _ c]; exact add_le_add_left a b h c

/-- An ordered monoid is a monoid with a partial order such that multiplication is monotone. -/
@[to_additive]
class IsOrderedMonoid (α : Type*) [CommMonoid α] [PartialOrder α] where
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b
  protected mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c, a * c ≤ b * c := fun a b h c ↦ by
    rw [mul_comm _ c, mul_comm _ c]; exact mul_le_mul_left a b h c

section IsOrderedMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]

@[to_additive]
instance (priority := 900) IsOrderedMonoid.toMulLeftMono : MulLeftMono α where
  elim := fun a _ _ bc ↦ IsOrderedMonoid.mul_le_mul_left _ _ bc a

@[to_additive]
instance (priority := 900) IsOrderedMonoid.toMulRightMono : MulRightMono α where
  elim := fun a _ _ bc ↦ IsOrderedMonoid.mul_le_mul_right _ _ bc a

end IsOrderedMonoid

/-- An ordered cancellative additive monoid is an ordered additive
monoid in which addition is cancellative and monotone. -/
class IsOrderedCancelAddMonoid (α : Type*) [AddCommMonoid α] [PartialOrder α] extends
    IsOrderedAddMonoid α where
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
  protected le_of_add_le_add_right : ∀ a b c : α, b + a ≤ c + a → b ≤ c := fun a b c h ↦ by
    rw [add_comm _ a, add_comm _ a] at h; exact le_of_add_le_add_left a b c h

/-- An ordered cancellative monoid is an ordered monoid in which
multiplication is cancellative and monotone. -/
@[to_additive IsOrderedCancelAddMonoid]
class IsOrderedCancelMonoid (α : Type*) [CommMonoid α] [PartialOrder α] extends
    IsOrderedMonoid α where
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
  protected le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c := fun a b c h ↦ by
    rw [mul_comm _ a, mul_comm _ a] at h; exact le_of_mul_le_mul_left a b c h

section IsOrderedCancelMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 200) IsOrderedCancelMonoid.toMulLeftReflectLE :
    MulLeftReflectLE α :=
  ⟨IsOrderedCancelMonoid.le_of_mul_le_mul_left⟩

@[to_additive]
instance (priority := 900) IsOrderedCancelMonoid.toMulLeftReflectLT :
    MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

@[to_additive]
theorem IsOrderedCancelMonoid.toMulRightReflectLT :
    MulRightReflectLT α :=
  inferInstance

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) IsOrderedCancelMonoid.toIsCancelMul : IsCancelMul α where
  mul_left_cancel _ _ _ h :=
    (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge
  mul_right_cancel _ _ _ h :=
    (le_of_mul_le_mul_right' h.le).antisymm <| le_of_mul_le_mul_right' h.ge

@[to_additive]
theorem IsOrderedCancelMonoid.of_mul_lt_mul_left {α : Type*} [CommMonoid α] [LinearOrder α]
    (hmul : ∀ a b c : α, b < c → a * b < a * c) : IsOrderedCancelMonoid α where
  mul_le_mul_left a b h c := by
    obtain rfl | h := eq_or_lt_of_le h
    · simp
    exact (hmul _ _ _ h).le
  le_of_mul_le_mul_left a b c h := by
    contrapose! h
    exact hmul _ _ _ h

end IsOrderedCancelMonoid

attribute [nolint docBlame]
  LinearOrderedAddCommMonoid.toLinearOrder
  LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid
  LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid
  LinearOrderedCommMonoid.toLinearOrder

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

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
