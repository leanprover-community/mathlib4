/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Data.Nat.Order.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

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
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals (exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.1⟩)
  -- ⊢ some val✝ + none = 0 ↔ some val✝ = 0 ∧ none = 0
  exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.2⟩
  -- ⊢ some val✝¹ + some val✝ = 0 ↔ some val✝¹ = 0 ∧ some val✝ = 0
  repeat' erw [WithBot.coe_eq_coe]
  -- ⊢ (fun x x_1 => x + x_1) val✝¹ val✝ = 0 ↔ val✝¹ = 0 ∧ val✝ = 0
  exact add_eq_zero_iff' (zero_le _) (zero_le _)
  -- 🎉 no goals
#align nat.with_bot.add_eq_zero_iff Nat.WithBot.add_eq_zero_iff

theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals refine' ⟨fun h => Option.noConfusion h, fun h => _⟩; aesop
  -- ⊢ some val✝¹ + some val✝ = 1 ↔ some val✝¹ = 0 ∧ some val✝ = 1 ∨ some val✝¹ = 1 …
  repeat' erw [WithBot.coe_eq_coe]
  -- ⊢ (fun x x_1 => x + x_1) val✝¹ val✝ = 1 ↔ val✝¹ = 0 ∧ val✝ = 1 ∨ val✝¹ = 1 ∧ v …
  exact Nat.add_eq_one_iff
  -- 🎉 no goals
#align nat.with_bot.add_eq_one_iff Nat.WithBot.add_eq_one_iff

theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals refine' ⟨fun h => Option.noConfusion h, fun h => _⟩; aesop
  -- ⊢ some val✝¹ + some val✝ = 2 ↔ some val✝¹ = 0 ∧ some val✝ = 2 ∨ some val✝¹ = 1 …
  repeat' erw [WithBot.coe_eq_coe]
  -- ⊢ (fun x x_1 => x + x_1) val✝¹ val✝ = ↑2 ↔ val✝¹ = 0 ∧ val✝ = ↑2 ∨ val✝¹ = 1 ∧ …
  exact Nat.add_eq_two_iff
  -- 🎉 no goals
#align nat.with_bot.add_eq_two_iff Nat.WithBot.add_eq_two_iff

theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals refine' ⟨fun h => Option.noConfusion h, fun h => _⟩; aesop
  -- ⊢ some val✝¹ + some val✝ = 3 ↔ some val✝¹ = 0 ∧ some val✝ = 3 ∨ some val✝¹ = 1 …
  repeat' erw [WithBot.coe_eq_coe]
  -- ⊢ (fun x x_1 => x + x_1) val✝¹ val✝ = ↑3 ↔ val✝¹ = 0 ∧ val✝ = ↑3 ∨ val✝¹ = 1 ∧ …
  exact Nat.add_eq_three_iff
  -- 🎉 no goals
#align nat.with_bot.add_eq_three_iff Nat.WithBot.add_eq_three_iff

theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero]
  -- ⊢ ↑0 ≤ ↑n
  exact WithBot.coe_le_coe.mpr (Nat.zero_le n)
  -- 🎉 no goals
#align nat.with_bot.coe_nonneg Nat.WithBot.coe_nonneg

@[simp]
theorem lt_zero_iff (n : WithBot ℕ) : n < 0 ↔ n = ⊥ := by
 refine' Option.casesOn n _ _
 -- ⊢ none < 0 ↔ none = ⊥
 exact of_eq_true (eq_true_of_decide (Eq.refl true))
 -- ⊢ ∀ (val : ℕ), some val < 0 ↔ some val = ⊥
 intro n
 -- ⊢ some n < 0 ↔ some n = ⊥
 refine' ⟨fun h => _, fun h => _⟩
 -- ⊢ some n = ⊥
 exfalso
 -- ⊢ False
 · rw [WithBot.some_eq_coe] at h
   -- ⊢ False
   exact not_le_of_lt h WithBot.coe_nonneg
   -- 🎉 no goals
 · rw [h]
   -- ⊢ ⊥ < 0
   exact of_eq_true (eq_true_of_decide (Eq.refl true))
   -- 🎉 no goals
#align nat.with_bot.lt_zero_iff Nat.WithBot.lt_zero_iff

theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine' ⟨fun h => lt_of_lt_of_le (WithBot.coe_lt_coe.mpr zero_lt_one) h, fun h => _⟩
  -- ⊢ 1 ≤ x
  induction x using WithBot.recBotCoe
  -- ⊢ 1 ≤ ⊥
  · exact (not_lt_bot h).elim
    -- 🎉 no goals
  · exact WithBot.coe_le_coe.mpr (Nat.succ_le_iff.mpr (WithBot.coe_lt_coe.mp h))
    -- 🎉 no goals
#align nat.with_bot.one_le_iff_zero_lt Nat.WithBot.one_le_iff_zero_lt

theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)
                     -- 🎉 no goals
#align nat.with_bot.lt_one_iff_le_zero Nat.WithBot.lt_one_iff_le_zero

theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  -- ⊢ none + 1 ≤ m
  · exact bot_le
    -- 🎉 no goals
  cases m
  -- ⊢ some val✝ + 1 ≤ none
  exacts [(not_lt_bot h).elim, WithBot.some_le_some.2 (WithBot.some_lt_some.1 h)]
  -- 🎉 no goals
#align nat.with_bot.add_one_le_of_lt Nat.WithBot.add_one_le_of_lt

end WithBot

end Nat
