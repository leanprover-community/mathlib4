/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.FinCases

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace PMF

open ENNReal NNReal
/-- The binomial `PMF`: the probability of observing exactly `i` “heads” in a sequence of `n`
independent coin tosses, each having probability `p` of coming up “heads”. -/
def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
      ↑(p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ))) (by
    dsimp only
    norm_cast
    convert (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    · rw [add_tsub_cancel_of_le (mod_cast h), one_pow])

theorem binomial_apply (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := by
  simp [binomial]

@[simp]
theorem binomial_apply_zero (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n 0 = (1 - p) ^ n := by
  simp [binomial_apply]

@[simp]
theorem binomial_apply_last (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by
  simp [binomial_apply]

theorem binomial_apply_self (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by simp

/-- The binomial distribution on one coin is the Bernoulli distribution. -/
theorem binomial_one_eq_bernoulli (p : ℝ≥0) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [binomial_apply]

theorem binomial_apply_of_le {k b : ℕ} (hb : k ≤ b) {x : ℝ≥0} (h : x ≤ 1) :
    ENNReal.ofReal ((b.choose k) * x ^ k * (1 - x) ^ (b - k))
    = PMF.binomial x h b (Fin.ofNat (b + 1) k) := by
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (x : ℝ≥0∞) = ENNReal.ofReal (1 - x : ℝ) := by norm_cast
  have : (1 - (x : ℝ)) ≥ 0 := by simpa
  rwa [Fin.ofNat_eq_cast, PMF.binomial_apply, Fin.val_natCast, Fin.val_last, eq0, eq1,
    coe_nnreal_eq x, mul_rotate, ofReal_mul, ofReal_mul, ofReal_pow, ofReal_pow, ofReal_natCast]
  all_goals positivity

end PMF
