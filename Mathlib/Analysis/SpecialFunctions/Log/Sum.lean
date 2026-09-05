/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds on the partial sums of the logarithm

The partial sum `∑ n ∈ Finset.Ioc 0 N, Real.log n` equals `Real.log N !`. Comparing the sum with
the integral `∫ t in 1..x, Real.log t = x * log x - x + 1` yields crude upper and lower bounds of
the form `∑ n ∈ Ioc 0 ⌊x⌋₊, log n = x * log x - x + O(log x)`, which are convenient in analytic
number theory (for instance in the proof of Mertens' theorems).

## Main statements

* `sum_log_eq_log_factorial`: `∑ n ∈ Ioc 0 N, log n = log N !`.
* `sum_log_le` / `le_sum_log`: two-sided bounds on `∑ n ∈ Ioc 0 ⌊x⌋₊, log n`.
* `le_sum_log_nat`: a sharper lower bound `N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n` via Stirling.
-/

@[expose] public section

open Nat hiding log log_pos
open Finset Real intervalIntegral MeasureTheory

namespace Real

variable {x : ℝ} (N : ℕ)

/-- The partial sum of the logarithm is equal to the log of the factorial. -/
theorem sum_log_eq_log_factorial : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  rw [← prod_Ico_id_eq_factorial, ← log_prod (by intros; simp; grind), prod_natCast]
  rfl

/-- A crude upper bound on the partial sum of the logarithm. -/
theorem sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have : ⌊x⌋₊ ≤ x := floor_le (by linarith)
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in (1 : ℕ)..⌊x⌋₊, log t) + log x := by
      rw [← Icc_add_one_left_eq_Ioc, ← sum_Ico_add_eq_sum_Icc (by simpa)]
      gcongr
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico ‹_›
    _ ≤ (∫ t in 1..x, log t) + log x := by
      norm_cast; gcongr
      exact integral_mono_interval (by rfl) (mod_cast ‹_›) ‹_›
        (ae_restrict_of_forall_mem (by measurability) fun _ _ ↦ (log_pos (by grind)).le)
        intervalIntegrable_log'
    _ = _ := by simp; ring

/-- An even cruder upper bound on the partial sum of the logarithm. -/
theorem sum_log_le' (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := by
  linarith [sum_log_le hx, log_le_sub_one_of_pos (by linarith)]

/-- A crude lower bound on the partial sum of the logarithm. -/
theorem le_sum_log (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
      rw [← Icc_add_one_left_eq_Ioc, zero_add, ← add_sum_Ioc_eq_sum_Icc this, cast_one,
        log_one, ← Ico_add_one_add_one_eq_Ioc, zero_add, ← sum_Ico_add']
      exact_mod_cast ((strictMonoOn_log.mono (by grind)).monotoneOn.integral_le_sum_Ico this).ge
    _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
      nth_rw 3 [integral_symm]
      rw [sub_neg_eq_add, integral_add_adjacent_intervals] <;> simp
    _ ≥ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log x := by
      gcongr
      apply integral_mono_on (floor_le (by linarith)) (by simp) (by simp)
      intro _ _; rify at this; gcongr <;> grind
    _ ≥ _ := by
      have := log_nonneg hx
      have : x - ⌊x⌋₊ ≤ 1 := by linarith [lt_floor_add_one x]
      grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul]
      nlinarith

/-- An even cruder lower bound on the partial sum of the logarithm. -/
theorem le_sum_log' (hx : 1 ≤ x) : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  linarith [le_sum_log hx, log_le_self (by linarith)]

/-- A sharper bound on the partial sum of the logarithm in the natural number case. -/
theorem le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 0 ≤ log N := by positivity
  have : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [two_le_pi])
  grw [sum_log_eq_log_factorial, ← Stirling.le_log_factorial_stirling hN]
  linarith

end Real
