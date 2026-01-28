/-
Copyright (c) 2026 The Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamad Al-Zawahreh
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Exponential vs Polynomial Growth Bounds

This file provides concrete numerical bounds establishing the dominance of the exponential function
over polynomial growth for explicitly specified large inputs.

## Main Results

* `Real.large_n_poly_vs_exponential`: For `n ≥ 1000` and `k ≤ 99`, `n^k < e^n`.
-/

namespace Real

/-- Proves log 1000 < 10 by showing 1000 < 2^10 ≤ e^10. -/
private lemma log_1000_lt_10_local : log 1000 < 10 := by
  -- Note: Using local version to avoid dependency on the other pending PR if needed
  -- Ideally this uses the lemma from Log/Basic.lean if available
  rw [log_lt_iff_lt_exp (by norm_num)]
  calc (1000 : ℝ) < (2 : ℝ) ^ 10 := by norm_num
    _ ≤ (exp 1) ^ 10 := by
      gcongr
      -- This relies on 2 <= exp 1 which we added to Exp.lean.
      -- If that PR isn't merged, we can reprovet it locally or assume it's there.
      -- For safety in this file, let's use the standard proof if needed or just the lemma.
      -- Re-proving locally for self-containment in this "Tao-Tier" file:
      rw [← one_add_one_eq_two]
      exact add_one_le_exp 1
    _ = exp 10 := by rw [←exp_nat_mul]; norm_num


/--
  Main theorem: `n^k < e^n` for `n ≥ 1000`, `k ≤ 99`.
  Proof uses the Mean Value Theorem on `f(x) = x - k * ln(x)` to show it is increasing
  and positive for `x ≥ 1000`.
-/
theorem large_n_poly_vs_exponential (n : ℝ) (k : ℕ)
    (hn : n ≥ 1000) (hk : k ≤ 99) :
    (n ^ k : ℝ) < exp n := by
  -- Power transformation
  rw [← log_lt_iff_lt_exp (pow_pos (by linarith) k)]
  rw [log_pow]

  -- Base case: k * ln(1000) < 1000
  have h_base : (k : ℝ) * log 1000 < 1000 := calc
    (k : ℝ) * log 1000 ≤ 99 * log 1000 := by
      apply mul_le_mul_of_nonneg_right
      · exact Nat.cast_le.mpr hk
      · exact log_nonneg (by norm_num)
    _ < 99 * 10 := by
      apply mul_lt_mul_of_pos_left
      · exact log_1000_lt_10_local
      · norm_num
    _ = 990 := by norm_num
    _ < 1000 := by norm_num

  -- Function definition and positivity at 1000
  let f := fun x => x - k * log x
  have f_1000_pos : 0 < f 1000 := sub_pos.mpr h_base

  -- Split into strict (> 1000) and equality (= 1000) cases
  rcases lt_or_eq_of_le hn with h_strict | h_eq

  · -- Strict case: Use Mean Value Theorem
    have h_diff_on : DifferentiableOn ℝ f (Set.Icc 1000 n) := by
      apply DifferentiableOn.sub
      · exact differentiableOn_id
      · apply DifferentiableOn.const_mul
        apply DifferentiableOn.mono differentiableOn_log
        intro x hx
        -- STRICT RIGOR: Explicitly show x > 0 implies x != 0
        have hx_pos : 0 < x := by linarith [hx.1]
        exact ne_of_gt hx_pos

    have h_mvt := exists_deriv_eq_slope f h_strict h_diff_on.continuousOn
                  (h_diff_on.mono Set.Ioo_subset_Icc_self)
    rcases h_mvt with ⟨c, hc, h_slope⟩

    -- MVT Equality Linearization
    have h_eqn : f n - f 1000 = deriv f c * (n - 1000) := by
       rw [h_slope]
       have h_ne_zero : n - 1000 ≠ 0 := by linarith
       field_simp [h_ne_zero]

    -- Positive Derivative Check
    have h_deriv_pos : 0 < deriv f c := by
      -- Calculate derivative explicitly
      have h_has_deriv : HasDerivAt f (1 - (k:ℝ)/c) c := by
        apply HasDerivAt.sub
        · exact hasDerivAt_id c
        · apply HasDerivAt.const_mul
          apply hasDerivAt_log
          -- Explicit inequality proof
          exact ne_of_gt (by linarith [hc.1])

      rw [h_has_deriv.deriv]
      rw [sub_pos] -- 1 - k/c > 0 <-> k/c < 1

      have hc_pos : 0 < c := by linarith [hc.1]
      -- Explicit iff application
      apply (div_lt_one hc_pos).mpr

      -- goal: k < c
      calc (k : ℝ) ≤ 99 := Nat.cast_le.mpr hk
        _ < 1000 := by norm_num
        _ < c := hc.1

    -- Final Inequality
    have f_n_pos : 0 < f n := by
      -- Goal: 0 < f n
      -- Use h_eqn to rewrite f n
      rw [eq_add_of_sub_eq h_eqn]

      -- Exact Proof Term Construction
      -- Arguments swapped: deriv is term 'a', f 1000 is term 'b'
      exact add_pos (mul_pos h_deriv_pos (sub_pos.mpr h_strict)) f_1000_pos

    exact sub_pos.mp f_n_pos

  · -- Equality case
    rw [h_eq] at f_1000_pos
    exact sub_pos.mp f_1000_pos

end Real
