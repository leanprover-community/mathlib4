/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson, Patrick Massot
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Order.Filter.Basic

#align_import combinatorics.derangements.exponential from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `numDerangements_tendsto_inv_e`.
-/


open Filter

open scoped BigOperators

open scoped Topology

theorem numDerangements_tendsto_inv_e :
    Tendsto (fun n => (numDerangements n : ℝ) / n.factorial) atTop (𝓝 (Real.exp (-1))) := by
  -- we show that d(n)/n! is the partial sum of exp(-1), but offset by 1.
  -- this isn't entirely obvious, since we have to ensure that asc_factorial and
  -- factorial interact in the right way, e.g., that k ≤ n always
  let s : ℕ → ℝ := fun n => ∑ k in Finset.range n, (-1 : ℝ) ^ k / k.factorial
  -- ⊢ Tendsto (fun n => ↑(numDerangements n) / ↑(Nat.factorial n)) atTop (𝓝 (Real. …
  suffices ∀ n : ℕ, (numDerangements n : ℝ) / n.factorial = s (n + 1) by
    simp_rw [this]
    -- shift the function by 1, and then use the fact that the partial sums
    -- converge to the infinite sum
    rw [tendsto_add_atTop_iff_nat
      (f := fun n => ∑ k in Finset.range n, (-1 : ℝ) ^ k / k.factorial) 1]
    apply HasSum.tendsto_sum_nat
    -- there's no specific lemma for ℝ that ∑ x^k/k! sums to exp(x), but it's
    -- true in more general fields, so use that lemma
    rw [Real.exp_eq_exp_ℝ]
    exact expSeries_div_hasSum_exp ℝ (-1 : ℝ)
  intro n
  -- ⊢ ↑(numDerangements n) / ↑(Nat.factorial n) = s (n + 1)
  rw [← Int.cast_ofNat, numDerangements_sum]
  -- ⊢ ↑(∑ k in Finset.range (n + 1), (-1) ^ k * ↑(Nat.ascFactorial k (n - k))) / ↑ …
  push_cast
  -- ⊢ (∑ x in Finset.range (n + 1), (-1) ^ x * ↑(Nat.ascFactorial x (n - x))) / ↑( …
  rw [Finset.sum_div]
  -- ⊢ ∑ x in Finset.range (n + 1), (-1) ^ x * ↑(Nat.ascFactorial x (n - x)) / ↑(Na …
  -- get down to individual terms
  refine' Finset.sum_congr (refl _) _
  -- ⊢ ∀ (x : ℕ), x ∈ Finset.range (n + 1) → (-1) ^ x * ↑(Nat.ascFactorial x (n - x …
  intro k hk
  -- ⊢ (-1) ^ k * ↑(Nat.ascFactorial k (n - k)) / ↑(Nat.factorial n) = (-1) ^ k / ↑ …
  have h_le : k ≤ n := Finset.mem_range_succ_iff.mp hk
  -- ⊢ (-1) ^ k * ↑(Nat.ascFactorial k (n - k)) / ↑(Nat.factorial n) = (-1) ^ k / ↑ …
  rw [Nat.ascFactorial_eq_div, add_tsub_cancel_of_le h_le]
  -- ⊢ (-1) ^ k * ↑(Nat.factorial n / Nat.factorial k) / ↑(Nat.factorial n) = (-1)  …
  push_cast [Nat.factorial_dvd_factorial h_le]
  -- ⊢ (-1) ^ k * (↑(Nat.factorial n) / ↑(Nat.factorial k)) / ↑(Nat.factorial n) =  …
  field_simp [Nat.factorial_ne_zero]
  -- ⊢ (-1) ^ k * ↑(Nat.factorial n) * ↑(Nat.factorial k) = (-1) ^ k * (↑(Nat.facto …
  ring
  -- 🎉 no goals
#align num_derangements_tendsto_inv_e numDerangements_tendsto_inv_e
