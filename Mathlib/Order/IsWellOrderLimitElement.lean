/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.WellFounded

/-!
# Limit elements in well-ordered types

This file introduces two main definitions:
- `wellOrderSucc a`: the successor of an element `a` in a well-ordered type
- the typeclass `IsWellOrderLimitElement a` which asserts that an element `a` (in a
well-ordered type) is neither a successor nor the smallest element, i.e. `a` is a limit element

Then, the lemma `eq_bot_or_eq_succ_or_isWellOrderLimitElement` shows that an element
in a well-ordered type is either `⊥`, a successor, or a limit element.

-/

variable {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]

/-- Given an element `a : α` in a well ordered set, this is the successor of `a`,
i.e. the smallest element stricly greater than `a` if it exists (or `a` itself otherwise). -/
noncomputable def wellOrderSucc (a : α) : α :=
  (IsWellFounded.wf (r := (· < ·))).succ a

lemma self_le_wellOrderSucc (a : α) : a ≤ wellOrderSucc a := by
  by_cases h : ∃ b, a < b
  · exact (IsWellFounded.wf.lt_succ h).le
  · dsimp [wellOrderSucc, WellFounded.succ]
    rw [dif_neg h]

lemma wellOrderSucc_le {a b : α} (ha : a < b) : wellOrderSucc a ≤ b := by
  dsimp [wellOrderSucc, WellFounded.succ]
  rw [dif_pos ⟨_, ha⟩]
  exact WellFounded.min_le _ ha

lemma self_lt_wellOrderSucc {a b : α} (h : a < b) : a < wellOrderSucc a :=
  IsWellFounded.wf.lt_succ ⟨b, h⟩

lemma le_of_lt_wellOrderSucc {a b : α} (h : a < wellOrderSucc b) : a ≤ b := by
  by_contra!
  simpa using lt_of_lt_of_le h (wellOrderSucc_le this)

/-- This property of an element `a : α` in a well-ordered type holds iff `a` is a
limit element, i.e. it is not a successor and it is not the smallest element of `α`. -/
class IsWellOrderLimitElement (a : α) : Prop where
  not_bot : ∃ (b : α), b < a
  not_succ (b : α) (hb : b < a) : ∃ (c : α), b < c ∧ c < a

variable (a : α) [ha : IsWellOrderLimitElement a]

lemma IsWellOrderLimitElement.neq_bot [OrderBot α] : a ≠ ⊥ := by
  rintro rfl
  obtain ⟨b, hb⟩ := ha.not_bot
  simp at hb

lemma IsWellOrderLimitElement.bot_lt [OrderBot α] : ⊥ < a := by
  obtain h|h := eq_or_lt_of_le (@bot_le _ _ _ a)
  · exact (IsWellOrderLimitElement.neq_bot a h.symm).elim
  · exact h

variable {a}

lemma IsWellOrderLimitElement.wellOrderSucc_lt {b : α} (hb : b < a) :
    wellOrderSucc b < a := by
  obtain ⟨c, hc₁, hc₂⟩ := ha.not_succ b hb
  exact lt_of_le_of_lt (wellOrderSucc_le hc₁) hc₂

lemma eq_bot_or_eq_succ_or_isWellOrderLimitElement [OrderBot α] (a : α) :
    a = ⊥ ∨ (∃ b, a = wellOrderSucc b ∧ b < a) ∨ IsWellOrderLimitElement a := by
  refine or_iff_not_imp_left.2 <| fun h₁ ↦ or_iff_not_imp_left.2 <| fun h₂ ↦ ?_
  refine (IsWellOrderLimitElement.mk ⟨⊥, Ne.bot_lt h₁⟩ fun b hb ↦ ?_)
  obtain rfl | h₃ := eq_or_lt_of_le (wellOrderSucc_le hb)
  · exact (h₂ ⟨b, rfl, hb⟩).elim
  · exact ⟨wellOrderSucc b, self_lt_wellOrderSucc hb, h₃⟩

lemma IsWellOrderLimitElement.neq_succ (a : α) (ha : a < wellOrderSucc a)
    [IsWellOrderLimitElement (wellOrderSucc a)] : False := by
  simpa using IsWellOrderLimitElement.wellOrderSucc_lt ha

@[simp]
lemma Nat.wellOrderSucc_eq (a : ℕ) : wellOrderSucc a = succ a :=
  le_antisymm (wellOrderSucc_le (Nat.lt_succ_self a))
    (Nat.succ_le.1 (self_lt_wellOrderSucc (Nat.lt_succ_self a)))

lemma Nat.not_isWellOrderLimitElement (a : ℕ) [IsWellOrderLimitElement a] : False := by
  obtain _|a := a
  · simpa using IsWellOrderLimitElement.neq_bot (0 : ℕ)
  · simpa using IsWellOrderLimitElement.wellOrderSucc_lt (Nat.lt_succ_self a)
