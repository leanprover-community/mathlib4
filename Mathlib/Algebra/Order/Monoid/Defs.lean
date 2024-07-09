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

@[to_additive]
theorem OrderedCommMonoid.toCovariantClassRight (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  inferInstance
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

@[to_additive]
theorem OrderedCancelCommMonoid.toContravariantClassRight :
    ContravariantClass α α (swap (· * ·)) (· < ·) :=
  inferInstance
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

#noalign bit0_pos

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

/--
The additive equivalent of `MulZeroClass`
-/
class IsTopAbsorbing (α : Type*) [Add α] [Top α] : Prop where
  /-- Top is a left aborbing element for addition -/
  top_add : ∀ a : α, ⊤ + a = ⊤
  /-- Top is a right aborbing element for addition -/
  add_top : ∀ a : α, a + ⊤ = ⊤

export IsTopAbsorbing (top_add add_top)
attribute [simp] top_add add_top

class IsBotAbsorbing (α : Type*) [Add α] [Bot α] : Prop where
  /-- Bot is a left aborbing element for addition -/
  bot_add : ∀ a : α, ⊥ + a = ⊥
  /-- Bot is a right aborbing element for addition -/
  add_bot : ∀ a : α, a + ⊥ = ⊥

export IsBotAbsorbing (bot_add add_bot)
attribute [simp] bot_add add_bot

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    OrderTop α, IsTopAbsorbing α where
  add_top a := add_comm a ⊤ ▸ top_add a
#align linear_ordered_add_comm_monoid_with_top LinearOrderedAddCommMonoidWithTop
#align linear_ordered_add_comm_monoid_with_top.to_order_top LinearOrderedAddCommMonoidWithTop.toOrderTop

class NoTopAddends (α : Type*) [Add α] [Top α] where
  eq_top_or_eq_top_of_add_eq_top : ∀ {a b : α}, a + b = ⊤ → a = ⊤ ∨ b = ⊤

export NoTopAddends (eq_top_or_eq_top_of_add_eq_top)

class NoBotAddends (α : Type*) [Add α] [Bot α] where
  eq_bot_or_eq_bot_of_add_eq_bot : ∀ {a b : α}, a + b = ⊥ → a = ⊥ ∨ b = ⊥

export NoBotAddends (eq_bot_or_eq_bot_of_add_eq_bot)

section NoTopAddends

variable {α : Type*} [Add α] [Top α] [IsTopAbsorbing α] [NoTopAddends α]

@[simp]
lemma add_eq_top {a b : α} :
    a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ where
  mp := eq_top_or_eq_top_of_add_eq_top
  mpr h := by cases h <;> simp_all

@[simp]
lemma top_eq_add {a b : α} :
    ⊤ = a + b ↔ a = ⊤ ∨ b = ⊤ := Eq.comm.trans add_eq_top

lemma add_ne_top {a b : α} :
    a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp

lemma top_ne_add {a b : α} :
    ⊤ ≠ a + b ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp

@[simp]
lemma add_lt_top {α : Type*} [PartialOrder α] [OrderTop α] [Add α]
    [IsTopAbsorbing α] [NoTopAddends α] {a b : α} :
    a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]

end NoTopAddends

section NoBotAddends

variable {α : Type*} [Add α] [Bot α] [IsBotAbsorbing α] [NoBotAddends α]

@[simp]
lemma add_eq_bot {a b : α} :
    a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ where
  mp := eq_bot_or_eq_bot_of_add_eq_bot
  mpr h := by cases h <;> simp_all

@[simp]
lemma bot_eq_add {a b : α} :
    ⊥ = a + b ↔ a = ⊥ ∨ b = ⊥ := Eq.comm.trans add_eq_bot

lemma add_ne_bot {a b : α} :
    a + b ≠ ⊥ ↔ a ≠ ⊥ ∧ b ≠ ⊥ := by simp

lemma bot_ne_add {a b : α} :
    ⊥ ≠ a + b ↔ a ≠ ⊥ ∧ b ≠ ⊥ := by simp

@[simp]
lemma bot_lt_add {α : Type*} [PartialOrder α] [OrderBot α] [Add α]
    [IsBotAbsorbing α] [NoBotAddends α] {a b : α} :
    ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b := by simp [bot_lt_iff_ne_bot]

end NoBotAddends

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
