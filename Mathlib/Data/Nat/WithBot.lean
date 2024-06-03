/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Order.Ring.Nat
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
  repeat (· exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.1⟩)
  · exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.2⟩
  repeat erw [WithBot.coe_eq_coe]
  exact add_eq_zero_iff' (zero_le _) (zero_le _)
#align nat.with_bot.add_eq_zero_iff Nat.WithBot.add_eq_zero_iff

theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  repeat refine ⟨fun h => Option.noConfusion h, fun h => ?_⟩;
              aesop (simp_config := { decide := true })
  repeat erw [WithBot.coe_eq_coe]
  exact Nat.add_eq_one_iff
#align nat.with_bot.add_eq_one_iff Nat.WithBot.add_eq_one_iff

theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  repeat refine ⟨fun h => Option.noConfusion h, fun h => ?_⟩;
              aesop (simp_config := { decide := true })
  repeat erw [WithBot.coe_eq_coe]
  exact Nat.add_eq_two_iff
#align nat.with_bot.add_eq_two_iff Nat.WithBot.add_eq_two_iff

theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  rcases n, m with ⟨_ | _, _ | _⟩
  repeat refine ⟨fun h => Option.noConfusion h, fun h => ?_⟩;
              aesop (simp_config := { decide := true })
  repeat erw [WithBot.coe_eq_coe]
  exact Nat.add_eq_three_iff
#align nat.with_bot.add_eq_three_iff Nat.WithBot.add_eq_three_iff

theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) := by
  rw [← WithBot.coe_zero]
  exact WithBot.coe_le_coe.mpr (Nat.zero_le n)
#align nat.with_bot.coe_nonneg Nat.WithBot.coe_nonneg

@[simp]
theorem lt_zero_iff {n : WithBot ℕ} : n < 0 ↔ n = ⊥ := WithBot.lt_coe_bot
#align nat.with_bot.lt_zero_iff Nat.WithBot.lt_zero_iff

theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x := by
  refine ⟨fun h => lt_of_lt_of_le (WithBot.coe_lt_coe.mpr zero_lt_one) h, fun h => ?_⟩
  induction x
  · exact (not_lt_bot h).elim
  · exact WithBot.coe_le_coe.mpr (Nat.succ_le_iff.mpr (WithBot.coe_lt_coe.mp h))
#align nat.with_bot.one_le_iff_zero_lt Nat.WithBot.one_le_iff_zero_lt

theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)
#align nat.with_bot.lt_one_iff_le_zero Nat.WithBot.lt_one_iff_le_zero

theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · exact bot_le
  cases m
  exacts [(not_lt_bot h).elim, WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 h)]
#align nat.with_bot.add_one_le_of_lt Nat.WithBot.add_one_le_of_lt

end WithBot

end Nat
