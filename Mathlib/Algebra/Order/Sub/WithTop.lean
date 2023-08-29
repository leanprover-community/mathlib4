/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

#align_import algebra.order.sub.with_top from "leanprover-community/mathlib"@"afdb4fa3b32d41106a4a09b371ce549ad7958abd"

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.
-/


variable {α β : Type*}

namespace WithTop

section

variable [Sub α] [Zero α]

/-- If `α` has subtraction and `0`, we can extend the subtraction to `WithTop α`. -/
protected def sub : ∀ _ _ : WithTop α, WithTop α
  | _, ⊤ => 0
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)
#align with_top.sub WithTop.sub

instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl
#align with_top.coe_sub WithTop.coe_sub

@[simp]
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl
#align with_top.top_sub_coe WithTop.top_sub_coe

@[simp]
theorem sub_top {a : WithTop α} : a - ⊤ = 0 := by cases a <;> rfl
                                                  -- ⊢ none - ⊤ = 0
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals
#align with_top.sub_top WithTop.sub_top

@[simp] theorem sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := by
  induction a using recTopCoe <;> induction b using recTopCoe <;>
  -- ⊢ ⊤ - b = ⊤ ↔ ⊤ = ⊤ ∧ b ≠ ⊤
                                  -- ⊢ ⊤ - ⊤ = ⊤ ↔ ⊤ = ⊤ ∧ ⊤ ≠ ⊤
                                  -- ⊢ ↑a✝ - ⊤ = ⊤ ↔ ↑a✝ = ⊤ ∧ ⊤ ≠ ⊤
    simp only [← coe_sub, coe_ne_top, sub_top, zero_ne_top, coe_ne_top, top_sub_coe, false_and,
      Ne.def]
#align with_top.sub_eq_top_iff WithTop.sub_eq_top_iff

theorem map_sub [Sub β] [Zero β] {f : α → β} (h : ∀ x y, f (x - y) = f x - f y) (h₀ : f 0 = 0) :
    ∀ x y : WithTop α, (x - y).map f = x.map f - y.map f
  | _, ⊤ => by simp only [h₀, sub_top, WithTop.map_zero, coe_zero, map_top]
               -- 🎉 no goals
  | ⊤, (x : α) => rfl
  | (x : α), (y : α) => by simp only [← coe_sub, map_coe, h]
                           -- 🎉 no goals
#align with_top.map_sub WithTop.map_sub

end

variable [CanonicallyOrderedAddMonoid α] [Sub α] [OrderedSub α]

instance : OrderedSub (WithTop α) := by
  constructor
  -- ⊢ ∀ (a b c : WithTop α), a - b ≤ c ↔ a ≤ c + b
  rintro x y z
  -- ⊢ x - y ≤ z ↔ x ≤ z + y
  induction y using WithTop.recTopCoe; · simp
  -- ⊢ x - ⊤ ≤ z ↔ x ≤ z + ⊤
                                         -- 🎉 no goals
  induction x using WithTop.recTopCoe; · simp
  -- ⊢ ⊤ - ↑a✝ ≤ z ↔ ⊤ ≤ z + ↑a✝
                                         -- 🎉 no goals
  induction z using WithTop.recTopCoe; · simp
  -- ⊢ ↑a✝ - ↑a✝¹ ≤ ⊤ ↔ ↑a✝ ≤ ⊤ + ↑a✝¹
                                         -- 🎉 no goals
  norm_cast; exact tsub_le_iff_right
  -- ⊢ a✝¹ - a✝² ≤ a✝ ↔ a✝¹ ≤ a✝ + a✝²
             -- 🎉 no goals

end WithTop
