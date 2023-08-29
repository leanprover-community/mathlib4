/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Basic

#align_import data.set.equitable from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Equitable functions

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the codomain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `SuccOrder` + `ConditionallyCompleteMonoid`, but we don't have the
latter yet.
-/


open BigOperators

variable {α β : Type*}

namespace Set

/-- A set is equitable if no element value is more than one bigger than another. -/
def EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1
#align set.equitable_on Set.EquitableOn

@[simp]
theorem equitableOn_empty [LE β] [Add β] [One β] (f : α → β) : EquitableOn ∅ f := fun a _ ha =>
  (Set.not_mem_empty a ha).elim
#align set.equitable_on_empty Set.equitableOn_empty

theorem equitableOn_iff_exists_le_le_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, b ≤ f a ∧ f a ≤ b + 1 := by
  refine' ⟨_, fun ⟨b, hb⟩ x y hx hy => (hb x hx).2.trans (add_le_add_right (hb y hy).1 _)⟩
  -- ⊢ EquitableOn s f → ∃ b, ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  -- ⊢ EquitableOn ∅ f → ∃ b, ∀ (a : α), a ∈ ∅ → b ≤ f a ∧ f a ≤ b + 1
  · simp
    -- 🎉 no goals
  intro hs
  -- ⊢ ∃ b, ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
  by_cases h : ∀ y ∈ s, f x ≤ f y
  -- ⊢ ∃ b, ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
    -- 🎉 no goals
  push_neg at h
  -- ⊢ ∃ b, ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
  obtain ⟨w, hw, hwx⟩ := h
  -- ⊢ ∃ b, ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
  refine' ⟨f w, fun y hy => ⟨Nat.le_of_succ_le_succ _, hs hy hw⟩⟩
  -- ⊢ Nat.succ (f w) ≤ Nat.succ (f y)
  rw [(Nat.succ_le_of_lt hwx).antisymm (hs hx hw)]
  -- ⊢ f x ≤ Nat.succ (f y)
  exact hs hx hy
  -- 🎉 no goals
#align set.equitable_on_iff_exists_le_le_add_one Set.equitableOn_iff_exists_le_le_add_one

theorem equitableOn_iff_exists_image_subset_icc {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, f '' s ⊆ Icc b (b + 1) := by
  simpa only [image_subset_iff] using equitableOn_iff_exists_le_le_add_one
  -- 🎉 no goals
#align set.equitable_on_iff_exists_image_subset_Icc Set.equitableOn_iff_exists_image_subset_icc

theorem equitableOn_iff_exists_eq_eq_add_one {s : Set α} {f : α → ℕ} :
    s.EquitableOn f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 := by
  simp_rw [equitableOn_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]
  -- 🎉 no goals
#align set.equitable_on_iff_exists_eq_eq_add_one Set.equitableOn_iff_exists_eq_eq_add_one

section OrderedSemiring

variable [OrderedSemiring β]

theorem Subsingleton.equitableOn {s : Set α} (hs : s.Subsingleton) (f : α → β) : s.EquitableOn f :=
  fun i j hi hj => by
  rw [hs hi hj]
  -- ⊢ f j ≤ f j + 1
  exact le_add_of_nonneg_right zero_le_one
  -- 🎉 no goals
#align set.subsingleton.equitable_on Set.Subsingleton.equitableOn

theorem equitableOn_singleton (a : α) (f : α → β) : Set.EquitableOn {a} f :=
  Set.subsingleton_singleton.equitableOn f
#align set.equitable_on_singleton Set.equitableOn_singleton

end OrderedSemiring

end Set

open Set

namespace Finset

variable {s : Finset α} {f : α → ℕ} {a : α}

theorem equitableOn_iff_le_le_add_one :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 := by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  -- ⊢ (∃ b, ∀ (a : α), a ∈ ↑s → b ≤ f a ∧ f a ≤ b + 1) ↔ ∀ (a : α), a ∈ s → (∑ i i …
  refine' ⟨_, fun h => ⟨_, h⟩⟩
  -- ⊢ (∃ b, ∀ (a : α), a ∈ ↑s → b ≤ f a ∧ f a ≤ b + 1) → ∀ (a : α), a ∈ s → (∑ i i …
  rintro ⟨b, hb⟩
  -- ⊢ ∀ (a : α), a ∈ s → (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) /  …
  by_cases h : ∀ a ∈ s, f a = b + 1
  -- ⊢ ∀ (a : α), a ∈ s → (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) /  …
  · intro a ha
    -- ⊢ (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) / card s + 1
    rw [h _ ha, sum_const_nat h, Nat.mul_div_cancel_left _ (card_pos.2 ⟨a, ha⟩)]
    -- ⊢ b + 1 ≤ b + 1 ∧ b + 1 ≤ b + 1 + 1
    exact ⟨le_rfl, Nat.le_succ _⟩
    -- 🎉 no goals
  push_neg at h
  -- ⊢ ∀ (a : α), a ∈ s → (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) /  …
  obtain ⟨x, hx₁, hx₂⟩ := h
  -- ⊢ ∀ (a : α), a ∈ s → (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) /  …
  suffices h : b = (∑ i in s, f i) / s.card
  -- ⊢ ∀ (a : α), a ∈ s → (∑ i in s, f i) / card s ≤ f a ∧ f a ≤ (∑ i in s, f i) /  …
  · simp_rw [← h]
    -- ⊢ ∀ (a : α), a ∈ s → b ≤ f a ∧ f a ≤ b + 1
    apply hb
    -- 🎉 no goals
  symm
  -- ⊢ (∑ i in s, f i) / card s = b
  refine'
    Nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum fun a ha => (hb a ha).1))
      ((sum_lt_sum (fun a ha => (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le _)
  rw [mul_comm, sum_const_nat]
  -- ⊢ ∀ (x : α), x ∈ s → b + 1 = Nat.succ b
  exact fun _ _ => rfl
  -- 🎉 no goals
#align finset.equitable_on_iff_le_le_add_one Finset.equitableOn_iff_le_le_add_one

theorem EquitableOn.le (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    (∑ i in s, f i) / s.card ≤ f a :=
  (equitableOn_iff_le_le_add_one.1 h a ha).1
#align finset.equitable_on.le Finset.EquitableOn.le

theorem EquitableOn.le_add_one (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
    f a ≤ (∑ i in s, f i) / s.card + 1 :=
  (equitableOn_iff_le_le_add_one.1 h a ha).2
#align finset.equitable_on.le_add_one Finset.EquitableOn.le_add_one

theorem equitableOn_iff :
    EquitableOn (s : Set α) f ↔
      ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
  by simp_rw [equitableOn_iff_le_le_add_one, Nat.le_and_le_add_one_iff]
     -- 🎉 no goals
#align finset.equitable_on_iff Finset.equitableOn_iff

end Finset
