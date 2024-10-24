/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Adjoining top/bottom elements to ordered monoids.
-/

universe u

variable {α : Type u}

open Function

namespace WithTop

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) where
  add_le_add_left _ _ := add_le_add_left

instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
    CanonicallyOrderedAddCommMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
    le_self_add := fun a b =>
      match a, b with
      | ⊤, ⊤ => le_rfl
      | (a : α), ⊤ => le_top
      | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
      | ⊤, (b : α) => le_rfl }

instance [CanonicallyLinearOrderedAddCommMonoid α] :
    CanonicallyLinearOrderedAddCommMonoid (WithTop α) :=
  { WithTop.canonicallyOrderedAddCommMonoid, WithTop.linearOrder with }

instance linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid,
    WithTop.isTopAbsorbing with }

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
  __ := WithTop.nontrivial
  sub_eq_add_neg a b := by
    cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel := by
    rintro (a | a) ha
    · exact (ha rfl).elim
    · exact (WithTop.coe_add ..).symm.trans (WithTop.coe_eq_coe.2 (add_neg_cancel a))

end LinearOrderedAddCommGroup

end WithTop

namespace WithBot

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) :=
  { WithBot.partialOrder, WithBot.addCommMonoid with
    add_le_add_left := fun _ _ h c => add_le_add_left h c }

instance linearOrderedAddCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with }

end WithBot
