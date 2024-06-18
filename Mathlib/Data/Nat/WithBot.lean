/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop

#align_import data.nat.with_bot from "leanprover-community/mathlib"@"966e0cf0685c9cedf8a3283ac69eef4d5f2eaca2"

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
  simp [← WithBot.coe_add, _root_.add_eq_zero_iff]
#align nat.with_bot.add_eq_zero_iff Nat.WithBot.add_eq_zero_iff

theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  cases n
  · simp only [WithBot.bot_add, WithBot.bot_ne_one, WithBot.bot_ne_zero, false_and, or_self]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_one_iff]
#align nat.with_bot.add_eq_one_iff Nat.WithBot.add_eq_one_iff

theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_two_iff]
#align nat.with_bot.add_eq_two_iff Nat.WithBot.add_eq_two_iff

theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]
#align nat.with_bot.add_eq_three_iff Nat.WithBot.add_eq_three_iff

theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero, cast_withBot, WithBot.coe_le_coe]
  exact n.zero_le
#align nat.with_bot.coe_nonneg Nat.WithBot.coe_nonneg

@[simp]
theorem lt_zero_iff {n : WithBot ℕ} : n < 0 ↔ n = ⊥ := WithBot.lt_coe_bot
#align nat.with_bot.lt_zero_iff Nat.WithBot.lt_zero_iff

theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine ⟨zero_lt_one.trans_le, fun h => ?_⟩
  cases x
  · exact (not_lt_bot h).elim
  · rwa [← WithBot.coe_zero, WithBot.coe_lt_coe, ← Nat.add_one_le_iff, zero_add,
      ← WithBot.coe_le_coe, WithBot.coe_one] at h
#align nat.with_bot.one_le_iff_zero_lt Nat.WithBot.one_le_iff_zero_lt

theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)
#align nat.with_bot.lt_one_iff_le_zero Nat.WithBot.lt_one_iff_le_zero

theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h
#align nat.with_bot.add_one_le_of_lt Nat.WithBot.add_one_le_of_lt

end WithBot

end Nat
