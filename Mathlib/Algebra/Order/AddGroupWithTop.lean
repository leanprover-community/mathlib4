/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Linearly ordered commutative additive groups and monoids with a top element adjoined

This file sets up a special class of linearly ordered commutative additive monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative additive group Γ and formally adjoining a
top element: Γ ∪ {⊤}.

The disadvantage is that a type such as `ENNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

variable {α : Type*}

/--
Prop-valued mixin for the top element of an ordered additive monoid to be absorbing under addition.
This is the additive equivalent of `MulZeroClass` for `Top`.
-/
class IsTopAbsorbing (α : Type*) [Add α] [Top α] : Prop where
  /-- `⊤` is a left aborbing element for addition -/
  top_add : ∀ a : α, ⊤ + a = ⊤
  /-- `⊤` is a right aborbing element for addition -/
  add_top : ∀ a : α, a + ⊤ = ⊤

export IsTopAbsorbing (top_add add_top)
attribute [simp] top_add add_top

/--
Prop-valued mixin for the bot element of an ordered additive monoid to be absorbing under addition.
This is the additive equivalent of `MulZeroClass` for `Bot`.
-/
class IsBotAbsorbing (α : Type*) [Add α] [Bot α] : Prop where
  /-- `⊥` is a left aborbing element for addition -/
  bot_add : ∀ a : α, ⊥ + a = ⊥
  /-- `⊥` is a right aborbing element for addition -/
  add_bot : ∀ a : α, a + ⊥ = ⊥

export IsBotAbsorbing (bot_add add_bot)
attribute [simp] bot_add add_bot

/--
The additive equivalent of `NoZeroDivisors` for `Top`
-/
class NoTopSum (α : Type*) [Add α] [Top α] : Prop where
  eq_top_or_eq_top_of_add_eq_top : ∀ {a b : α}, a + b = ⊤ → a = ⊤ ∨ b = ⊤

export NoTopSum (eq_top_or_eq_top_of_add_eq_top)

/--
The additive equivalent of `NoZeroDivisors` for `Bot`
-/
class NoBotSum (α : Type*) [Add α] [Bot α] : Prop where
  eq_bot_or_eq_bot_of_add_eq_bot : ∀ {a b : α}, a + b = ⊥ → a = ⊥ ∨ b = ⊥

export NoBotSum (eq_bot_or_eq_bot_of_add_eq_bot)

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    OrderTop α, IsTopAbsorbing α where
  add_top a := add_comm a ⊤ ▸ top_add a

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommGroupWithTop (α : Type*) extends LinearOrderedAddCommMonoidWithTop α,
  SubNegMonoid α, Nontrivial α where
  protected neg_top : -(⊤ : α) = ⊤
  protected add_neg_cancel : ∀ a : α, a ≠ ⊤ → a + -a = 0

instance WithTop.linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
    top_add := WithTop.top_add }

namespace WithTop

open Function

namespace LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

instance instNeg : Neg (WithTop α) where neg := Option.map fun a : α => -a

/-- If `α` has subtraction, we can extend the subtraction to `WithTop α`, by
setting `x - ⊤ = ⊤` and `⊤ - x = ⊤`. This definition is only registered as an instance on linearly
ordered additive commutative groups, to avoid conflicting with the instance `WithTop.instSub` on
types with a bottom element. -/
protected def sub : ∀ _ _ : WithTop α, WithTop α
  | _, ⊤ => ⊤
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance instSub : Sub (WithTop α) where sub := WithTop.LinearOrderedAddCommGroup.sub

@[simp, norm_cast]
theorem coe_neg (a : α) : ((-a : α) : WithTop α) = -a :=
  rfl

@[simp]
theorem neg_top : -(⊤ : WithTop α) = ⊤ := rfl

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b := rfl

@[simp]
theorem top_sub {a : WithTop α} : (⊤ : WithTop α) - a = ⊤ := by
  cases a <;> rfl

@[simp]
theorem sub_top {a : WithTop α} : a - ⊤ = ⊤ := by cases a <;> rfl

@[simp]
lemma sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ (a = ⊤ ∨ b = ⊤) := by
  cases a <;> cases b <;> simp [← coe_sub]

instance : LinearOrderedAddCommGroupWithTop (WithTop α) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  __ := Option.nontrivial
  sub_eq_add_neg a b := by
    cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := Option.map_none
  zsmul := zsmulRec
  add_neg_cancel := by
    rintro (a | a) ha
    · exact (ha rfl).elim
    · exact (WithTop.coe_add ..).symm.trans (WithTop.coe_eq_coe.2 (add_neg_cancel a))

end LinearOrderedAddCommGroup

end WithTop

section NoTopSum

variable {α : Type*} [Add α] [Top α] [IsTopAbsorbing α] [NoTopSum α]

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
    [IsTopAbsorbing α] [NoTopSum α] {a b : α} :
    a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]

end NoTopSum

section NoBotSum

variable {α : Type*} [Add α] [Bot α] [IsBotAbsorbing α] [NoBotSum α]

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
    [IsBotAbsorbing α] [NoBotSum α] {a b : α} :
    ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b := by simp [bot_lt_iff_ne_bot]

end NoBotSum
