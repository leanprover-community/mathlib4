/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.

This file introduces a subtraction on `WithTop α` when `α` has a subtraction and a bottom element,
given by `x - ⊤ = ⊥` and `⊤ - x = ⊤`. This will be instantiated mostly for `ℕ∞` and `ℝ≥0∞`, where
the bottom element is zero.

Note that there is another subtraction on objects of the form `WithTop α` in the file
`Mathlib.Algebra.Order.Group.WithTop`, setting `-⊤ = ⊤` as this corresponds to the additivization
of the usual convention `0⁻¹ = 0` and is relevant in valuation theory. Since this other instance
is only registered for `LinearOrderedAddCommGroup α` (which doesn't have a bottom element, unless
the group is trivial), this shouldn't create diamonds.
-/

variable {α β : Type*}

namespace WithTop

section

variable [Sub α] [Bot α]

/-- If `α` has a subtraction and a bottom element, we can extend the subtraction to `WithTop α`, by
setting `x - ⊤ = ⊥` and `⊤ - x = ⊤`. -/
protected def sub : ∀ _ _ : WithTop α, WithTop α
  | _, ⊤ => (⊥ : α)
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[simp]
theorem sub_top {a : WithTop α} : a - ⊤ = (⊥ : α) := by cases a <;> rfl

@[simp] theorem sub_eq_top {a b : WithTop α} : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := by
  induction a <;> induction b <;>
    simp only [← coe_sub, coe_ne_top, sub_top, zero_ne_top, top_sub_coe, false_and, Ne,
      not_true_eq_false, not_false_eq_true, and_false, and_self]

lemma sub_ne_top {a b : WithTop α} : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := by simp [or_iff_not_imp_left]

theorem map_sub [Sub β] [Bot β] {f : α → β} (h : ∀ x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥) :
    ∀ x y : WithTop α, (x - y).map f = x.map f - y.map f
  | _, ⊤ => by simp only [sub_top, map_coe, h₀, map_top]
  | ⊤, (x : α) => rfl
  | (x : α), (y : α) => by simp only [← coe_sub, map_coe, h]

end

variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α]

instance : OrderedSub (WithTop α) := by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast; exact tsub_le_iff_right

end WithTop
