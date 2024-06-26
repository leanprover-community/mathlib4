/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

#align_import algebra.order.group.with_top from "leanprover-community/mathlib"@"f178c0e25af359f6cbc72a96a243efd3b12423a3"

/-!
# Adjoining a top element to a `LinearOrderedAddCommGroup`.

This file defines a negation on `WithTop α` when `α` is a linearly ordered additive commutative
group, by setting `-⊤ = ⊤`. This corresponds to the additivization of the usual multiplicative
convention `0⁻¹ = 0`, and is relevant in valuation theory.


Note that there is another subtraction on objects of the form `WithTop α` in the file
`Mathlib.Algebra.Order.Sub.WithTop`, setting `-⊤ = ⊥` when `α` has a bottom element. This is the
right convention for `ℕ∞` or `ℝ≥0∞`. Since `LinearOrderedAddCommGroup`s don't have a bottom element
(unless they are trivial), this shouldn't create diamonds.

To avoid conflicts between the two notions, we put everything in the current file in the namespace
`WithTop.LinearOrderedAddCommGroup`.
-/

namespace WithTop

variable {α : Type*}

namespace LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

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
#align with_top.coe_neg WithTop.LinearOrderedAddCommGroup.coe_neg

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
    · exact (WithTop.coe_add ..).symm.trans (WithTop.coe_eq_coe.2 (add_neg_self a))
#align with_top.linear_ordered_add_comm_group_with_top WithTop.LinearOrderedAddCommGroup.instLinearOrderedAddCommGroupWithTop

end LinearOrderedAddCommGroup

end WithTop
