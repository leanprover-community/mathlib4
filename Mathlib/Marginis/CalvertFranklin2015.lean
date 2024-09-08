/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence

/-!
This concerns the second sentence in the Introduction in the paper
Genericity and UD–random reals by WESLEY CALVERT, JOHANNA N.Y. FRANKLIN.
We define uniform distribution and prove that the constant 0 sequence is not uniformly distributed.
-/

open Finset

def uniformly_distributed (x : ℕ → Set.Ico (0:ℝ) 1) :=
  ∀ a b ε : ℝ, 0 ≤ a → a < b → b ≤ 1 → ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    abs (card (filter (λ i : Fin n ↦ a < x i ∧ x i < b) univ) - (b - a) * n) < n * ε

example : ¬ uniformly_distributed (λ _ ↦ ⟨0,by simp⟩) := by
  unfold uniformly_distributed
  push_neg
  use 1/2, 1, 1/2
  simp_all only [one_div, inv_nonneg, Nat.ofNat_nonneg, le_refl, gt_iff_lt, inv_pos, Nat.ofNat_pos,
    ge_iff_le, inv_lt_zero, zero_lt_one, and_true, filter_const, true_and]
  constructor
  · exact two_inv_lt_one
  · intro n₀;use n₀
    simp_all only [le_refl, true_and]
    rw [if_neg (by simp)]
    simp only [card_empty, CharP.cast_eq_zero, zero_sub, abs_neg]
    ring_nf
    exact le_abs_self _
