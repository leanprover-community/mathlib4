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

open Nat Real Filter Tendsto goldenRatio

/-- The limit of `fib (n + 1) / fib n` as `n → ∞` is the golden ratio. -/
theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n ↦ (fib (n + 1) / fib n : ℝ)) atTop <| nhds φ := by
  have h₁ n : (fib (n + 1) / fib n : ℝ) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field_simp
  have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) <| by
    rw [abs_div, div_lt_one <| by positivity, abs_of_pos goldenRatio_pos, abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring, funext h₁]
  exact const_sub _ (const_mul _ h₂) |>.div (const_sub _ h₂) <| by simp

/-- The limit of `fib n / fib (n + 1)` as `n → ∞` is the negative conjugate of the golden ratio. -/
theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n ↦ (fib n / fib (n + 1) : ℝ)) atTop <| nhds <| -ψ := by
  convert tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]
