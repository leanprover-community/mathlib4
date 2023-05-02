/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.RCongr.Basic

/-!
a lemma from the proof of IMO 2019 Q4
-/

open Nat BigOperators Finset

@[aesop unsafe 90% (rule_sets [rcongr]) apply]
theorem factorial_lt_of_lt {m n : ℕ} (hn : 0 < n) (h : n < m) : n ! < m ! := (factorial_lt hn).mpr h


example (n k : ℕ) (h2 : ∑ i in range n, i < k) (hn : 6 ≤ n) :
    ∏ i in range n, (2 ^ n - 2 ^ i : ℤ) < (k ! : ℤ) := by
  have le_sum : ∀ {N}, 6 ≤ N → 15 ≤ ∑ i in range N, i
  · intros N hN
    show ∑ i in range 6, i ≤_
    apply sum_le_sum_of_subset
    simpa using hN
  calc ∏ i in range n, (2 ^ n - 2 ^ i : ℤ)
      ≤ (∏ i in range n, 2 ^ n : ℤ) := ?_
    _ < (k ! : ℤ) := ?_
  · apply prod_le_prod
    · intro i hi
      have : (2:ℤ) ^ i ≤ 2 ^ n
      · -- `rcongrm 2 ^ _`
        refine pow_le_pow (by norm_num) (le_of_lt ?_)
        simpa using hi
      linarith
    · intros
      apply sub_le_self
      positivity
  norm_cast
  calc ∏ i in range n, 2 ^ n
      = 2 ^ (n * n) := by rw [prod_const, card_range, ← pow_mul]
    _ < (∑ i in range n, i) ! := ?_
    _ < k ! := by have := le_sum hn ; rcongr -- stated fact is used for positivity
  clear h2
  induction' n, hn using Nat.le_induction with n' hn' ih
  · calc 2 ^ (6 * 6) < 15! := by norm_num
      _ = (∑ i in range 6, i)! := by simp only [sum_range_succ, sum_range_zero]
  let A := ∑ i in range n', i
  calc 2 ^ ((n' + 1) * (n' + 1))
      ≤ 2 ^ (n' * n' + 4 * n') := ?_
    _ = 2 ^ (n' * n') * (2 ^ 4) ^ n' := by rw [← pow_mul, ← pow_add]
    _ < A ! * (2 ^ 4) ^ n' := by rcongr
    _ = A ! * (15 + 1) ^ n' := by rfl
    _ ≤ A ! * (A + 1) ^ n' := ?_
    _ ≤ (A + n')! := by apply factorial_mul_pow_le_factorial
    _ = (∑ i in range (n' + 1), i)! := by rw [sum_range_succ]
  · -- `rcongrm 2 ^ _`
    refine pow_le_pow_of_le_right (by positivity) ?_
    linarith
  · -- `rcongrm A! * (_ + 1) ^ n'`
    refine mul_le_mul_of_nonneg_left (Nat.pow_le_pow_of_le_left (add_le_add_right ?_ _) _) (by positivity)
    exact le_sum hn'
