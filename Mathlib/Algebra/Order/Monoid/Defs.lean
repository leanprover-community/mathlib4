/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/


open Function

variable {α : Type*}

/-- An ordered (additive) commutative monoid is a commutative monoid with a partial order such that
addition is monotone. -/
class OrderedAddCommMonoid (α : Type*) extends AddCommMonoid α, PartialOrder α where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

/-- An ordered commutative monoid is a commutative monoid with a partial order such that
multiplication is monotone. -/
@[to_additive]
class OrderedCommMonoid (α : Type*) extends CommMonoid α, PartialOrder α where
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b

section OrderedCommMonoid
variable [OrderedCommMonoid α]

@[to_additive]
instance OrderedCommMonoid.toCovariantClassLeft : CovariantClass α α (· * ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedCommMonoid.mul_le_mul_left _ _ bc a

@[to_additive]
theorem OrderedCommMonoid.toCovariantClassRight (M : Type*) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  inferInstance

end OrderedCommMonoid

/-- An ordered cancellative additive commutative monoid is a partially ordered commutative additive
monoid in which addition is cancellative and monotone. -/
class OrderedCancelAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α where
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid is a partially ordered commutative monoid in which
multiplication is cancellative and monotone. -/
@[to_additive OrderedCancelAddCommMonoid]
class OrderedCancelCommMonoid (α : Type*) extends OrderedCommMonoid α where
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.toContravariantClassLeLeft :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩

@[to_additive]
instance OrderedCancelCommMonoid.toContravariantClassLeft :
    ContravariantClass α α (· * ·) (· < ·) where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

@[to_additive]
theorem OrderedCancelCommMonoid.toContravariantClassRight :
    ContravariantClass α α (swap (· * ·)) (· < ·) :=
  inferInstance

-- See note [lower instance priority]
@[to_additive OrderedCancelAddCommMonoid.toCancelAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel :=
      fun _ _ _ h => (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }

end OrderedCancelCommMonoid

/-- A linearly ordered additive commutative monoid. -/
class LinearOrderedAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α, LinearOrder α

/-- A linearly ordered commutative monoid. -/
@[to_additive]
class LinearOrderedCommMonoid (α : Type*) extends OrderedCommMonoid α, LinearOrder α

/-- A linearly ordered cancellative additive commutative monoid is an additive commutative monoid
with a decidable linear order in which addition is cancellative and monotone. -/
class LinearOrderedCancelAddCommMonoid (α : Type*) extends OrderedCancelAddCommMonoid α,
    LinearOrderedAddCommMonoid α

/-- A linearly ordered cancellative commutative monoid is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[to_additive LinearOrderedCancelAddCommMonoid]
class LinearOrderedCancelCommMonoid (α : Type*) extends OrderedCancelCommMonoid α,
    LinearOrderedCommMonoid α

attribute [to_additive existing] LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid

/--
The additive equivalent of `MulZeroClass` for `Top`
-/
class IsTopAbsorbing (α : Type*) [Add α] [Top α] : Prop where
  /-- Top is a left aborbing element for addition -/
  top_add : ∀ a : α, ⊤ + a = ⊤
  /-- Top is a right aborbing element for addition -/
  add_top : ∀ a : α, a + ⊤ = ⊤

export IsTopAbsorbing (top_add add_top)
attribute [simp] top_add add_top

/--
The additive equivalent of `MulZeroClass` for `Bot`
-/
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

/--
The additive equivalent of `NoZeroDivisors` for `Top`
-/
class NoTopAddends (α : Type*) [Add α] [Top α] : Prop where
  eq_top_or_eq_top_of_add_eq_top : ∀ {a b : α}, a + b = ⊤ → a = ⊤ ∨ b = ⊤

export NoTopAddends (eq_top_or_eq_top_of_add_eq_top)

/--
The additive equivalent of `NoZeroDivisors` for `Bot`
-/
class NoBotAddends (α : Type*) [Add α] [Bot α] : Prop where
  eq_bot_or_eq_bot_of_add_eq_bot : ∀ {a b : α}, a + b = ⊥ → a = ⊥ ∨ b = ⊥

export NoBotAddends (eq_bot_or_eq_bot_of_add_eq_bot)

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
