/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.FinCases

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `Pmf.bernoulli`.
-/

namespace Pmf

open ENNReal

/-- The binomial `Pmf`: the probability of observing exactly `i` “heads” in a sequence of `n`
independent coin tosses, each having probability `p` of coming up “heads”. -/
noncomputable
def binomial (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : Pmf (Fin (n + 1)) :=
  .ofFintype (fun i => p^(i : ℕ) * (1-p)^((Fin.last n - i) : ℕ) * (n.choose i : ℕ)) (by
    convert (add_pow p (1-p) n).symm
    -- ⊢ (Finset.sum Finset.univ fun a => (fun i => p ^ ↑i * (1 - p) ^ (↑(Fin.last n) …
    · rw [Finset.sum_fin_eq_sum_range]
      -- ⊢ (Finset.sum (Finset.range (n + 1)) fun i => if h : i < n + 1 then (fun i =>  …
      apply Finset.sum_congr rfl
      -- ⊢ ∀ (x : ℕ), x ∈ Finset.range (n + 1) → (if h : x < n + 1 then (fun i => p ^ ↑ …
      intro i hi
      -- ⊢ (if h : i < n + 1 then (fun i => p ^ ↑i * (1 - p) ^ (↑(Fin.last n) - ↑i) * ↑ …
      rw [Finset.mem_range] at hi
      -- ⊢ (if h : i < n + 1 then (fun i => p ^ ↑i * (1 - p) ^ (↑(Fin.last n) - ↑i) * ↑ …
      rw [dif_pos hi, Fin.last]
      -- 🎉 no goals
    · simp [h])
      -- 🎉 no goals

theorem binomial_apply (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p^(i : ℕ) * (1-p)^((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := rfl

@[simp]
theorem binomial_apply_zero (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) :
    binomial p h n 0 = (1-p)^n := by
  simp [binomial_apply]
  -- 🎉 no goals

@[simp]
theorem binomial_apply_self (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) :
    binomial p h n n = p^n := by
  simp [binomial_apply, Nat.mod_eq_of_lt]
  -- 🎉 no goals

/-- The binomial distribution on one coin is the bernoully distribution. -/
theorem binomial_one_eq_bernoulli (p : ℝ≥0∞) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [tsum_bool, binomial_apply]
  -- ⊢ ↑(binomial p h 1) i = ↑(map (fun x => bif x then 1 else 0) (bernoulli p h)) i
         -- ⊢ ↑(binomial p h 1) { val := 0, isLt := (_ : 0 < 1 + 1) } = ↑(map (fun x => bi …
                         -- 🎉 no goals
                         -- 🎉 no goals

end Pmf
