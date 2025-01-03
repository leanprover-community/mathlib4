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

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends LinearOrderedAddCommMonoid α,
    OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommGroupWithTop (α : Type*) extends LinearOrderedAddCommMonoidWithTop α,
  SubNegMonoid α, Nontrivial α where
  protected neg_top : -(⊤ : α) = ⊤
  protected add_neg_cancel : ∀ a : α, a ≠ ⊤ → a + -a = 0

instance WithTop.linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
    top_add' := WithTop.top_add }

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α]

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

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

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b : α}

attribute [simp] LinearOrderedAddCommGroupWithTop.neg_top

lemma add_neg_cancel_of_ne_top {α : Type*} [LinearOrderedAddCommGroupWithTop α]
    {a : α} (h : a ≠ ⊤) :
    a + -a = 0 :=
  LinearOrderedAddCommGroupWithTop.add_neg_cancel a h

@[simp]
lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  constructor
  · intro h
    by_contra nh
    rw [not_or] at nh
    replace h := congrArg (-a + ·) h
    dsimp only at h
    rw [add_top, ← add_assoc, add_comm (-a), add_neg_cancel_of_ne_top,
      zero_add] at h
    · exact nh.2 h
    · exact nh.1
  · rintro (rfl | rfl)
    · simp
    · simp

@[simp]
lemma top_ne_zero :
    (⊤ : α) ≠ 0 := by
  intro nh
  have ⟨a, b, h⟩ := Nontrivial.exists_pair_ne (α := α)
  have : a + 0 ≠ b + 0 := by simpa
  rw [← nh] at this
  simp at this

@[simp] lemma neg_eq_top {a : α} : -a = ⊤ ↔ a = ⊤ where
  mp h := by
    by_contra nh
    replace nh := add_neg_cancel_of_ne_top nh
    rw [h, add_top] at nh
    exact top_ne_zero nh
  mpr h := by simp [h]

instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg a := by
    by_cases h : a = ⊤
    · simp [h]
    · have h2 : ¬ -a = ⊤ := fun nh ↦ h <| neg_eq_top.mp nh
      replace h2 : a + (-a + - -a) = a + 0 := congrArg (a + ·) (add_neg_cancel_of_ne_top h2)
      rw [← add_assoc, add_neg_cancel_of_ne_top h] at h2
      simp only [zero_add, add_zero] at h2
      exact h2
  neg_add_rev a b := by
    by_cases ha : a = ⊤
    · simp [ha]
    by_cases hb : b = ⊤
    · simp [hb]
    apply (_ : Function.Injective (a + b + ·))
    · dsimp
      rw [add_neg_cancel_of_ne_top, ← add_assoc, add_assoc a,
        add_neg_cancel_of_ne_top hb, add_zero,
        add_neg_cancel_of_ne_top ha]
      simp [ha, hb]
    · apply Function.LeftInverse.injective (g := (-(a + b) + ·))
      intro x
      dsimp only
      rw [← add_assoc, add_comm (-(a + b)), add_neg_cancel_of_ne_top, zero_add]
      simp [ha, hb]
  neg_eq_of_add a b h := by
    have oh := congrArg (-a + ·) h
    dsimp only at oh
    rw [add_zero, ← add_assoc, add_comm (-a), add_neg_cancel_of_ne_top, zero_add] at oh
    · exact oh.symm
    intro v
    simp [v] at h

end LinearOrderedAddCommGroupWithTop
