/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.GoldenRatio

/-!
# The ratio of consecutive Fibonacci numbers

We prove that the ratio of consecutive Fibonacci numbers tends to the golden ratio.
-/

open Nat Real Filter goldenRatio

/-- The limit of `fib (n + 1) / fib n` as `n → ∞` is the golden ratio. -/
theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n ↦ (fib (n + 1) / fib n : ℝ)) atTop <| nhds φ := by
  have h₁ n (hn : n ≥ 1) : (fib n : ℝ)⁻¹ * ψ ^ n + φ = fib (n + 1) / fib n := by
    rw [← fib_succ_sub_goldenRatio_mul_fib, mul_comm, sub_mul, mul_assoc, Field.mul_inv_cancel,
      mul_one, sub_add_cancel, mul_comm, inv_mul_eq_div]
    simp only [ne_eq, cast_eq_zero, fib_eq_zero]
    cutsat
  have h₂ : ∀ᶠ n in atTop, |(fib n : ℝ)⁻¹| ≤ 1 :=
    Eventually.of_forall fun n ↦ by simp [cast_inv_le_one]
  convert Tendsto.congr' (eventually_atTop.mpr ⟨_, h₁⟩) <| Tendsto.add_const _ <|
    bdd_le_mul_tendsto_zero' _ h₂ <| tendsto_pow_atTop_nhds_zero_of_abs_lt_one <|
      abs_lt.mpr ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
  simp

/-- The limit of `fib n / fib (n + 1)` as `n → ∞` is the negative conjugate of the golden ratio. -/
theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n ↦ (fib n / fib (n + 1) : ℝ)) atTop <| nhds <| -ψ := by
  convert tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]
