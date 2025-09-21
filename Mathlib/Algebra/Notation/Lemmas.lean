/-
Copyright (c) 2023 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
import Batteries.Tactic.Init
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Util.AssertExists

/-! # Lemmas about inequalities with `1`. -/

assert_not_exists Monoid

variable {α : Type*}

section dite
variable [One α] {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α}

@[to_additive dite_nonneg]
lemma one_le_dite [LE α] (ha : ∀ h, 1 ≤ a h) (hb : ∀ h, 1 ≤ b h) : 1 ≤ dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
lemma dite_le_one [LE α] (ha : ∀ h, a h ≤ 1) (hb : ∀ h, b h ≤ 1) : dite p a b ≤ 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive dite_pos]
lemma one_lt_dite [LT α] (ha : ∀ h, 1 < a h) (hb : ∀ h, 1 < b h) : 1 < dite p a b := by
  split; exacts [ha ‹_›, hb ‹_›]

@[to_additive]
lemma dite_lt_one [LT α] (ha : ∀ h, a h < 1) (hb : ∀ h, b h < 1) : dite p a b < 1 := by
  split; exacts [ha ‹_›, hb ‹_›]

end dite

section
variable [One α] {p : Prop} [Decidable p] {a b : α}

@[to_additive ite_nonneg]
lemma one_le_ite [LE α] (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ ite p a b := by split <;> assumption

@[to_additive]
lemma ite_le_one [LE α] (ha : a ≤ 1) (hb : b ≤ 1) : ite p a b ≤ 1 := by split <;> assumption

@[to_additive ite_pos]
lemma one_lt_ite [LT α] (ha : 1 < a) (hb : 1 < b) : 1 < ite p a b := by split <;> assumption

@[to_additive]
lemma ite_lt_one [LT α] (ha : a < 1) (hb : b < 1) : ite p a b < 1 := by split <;> assumption

end
