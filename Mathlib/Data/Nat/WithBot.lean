/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Order.Nat

/-!
# `WithBot ℕ`

Lemmas about the type of natural numbers with a bottom element adjoined.
-/


namespace Nat

namespace WithBot

instance : WellFoundedRelation (WithBot ℕ) where
  rel := (· < ·)
  wf := IsWellFounded.wf

theorem add_eq_zero_iff {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, add_eq_zero_iff_of_nonneg]

theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  cases n
  · simp only [WithBot.bot_add, WithBot.bot_ne_one, WithBot.bot_ne_zero, false_and, or_self]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]

theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]

theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]

theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero, cast_withBot, WithBot.coe_le_coe]
  exact n.zero_le

@[simp]
theorem lt_zero_iff {n : WithBot ℕ} : n < 0 ↔ n = ⊥ := WithBot.lt_coe_bot

theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h

theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)

theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h

end WithBot

end Nat
