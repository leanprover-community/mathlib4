/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.GoldenRatio


open goldenRatio

/-- The limit of dividing consecutive Fibonacci numbers is the golden ratio. -/
theorem tendsto_fib_succ_div_fib_atTop :
    Filter.Tendsto (fun n ↦ (Nat.fib (n + 1) / Nat.fib n : ℝ)) Filter.atTop <| nhds φ := by
  have h n (hn : n ≥ 1) : (Nat.fib n : ℝ)⁻¹ * ψ ^ n + φ = Nat.fib (n + 1) / Nat.fib n := by
    rw [← Real.fib_succ_sub_goldenRatio_mul_fib, mul_sub]
    nth_rw 2 [mul_comm]
    rw [mul_assoc, Field.mul_inv_cancel, mul_one, sub_add_cancel, inv_mul_eq_div]
    simp [Nat.fib_eq_zero]
    bound
  refine Filter.Tendsto.congr' (Filter.eventually_atTop.mpr ⟨_, h⟩) ?_
  have : ∀ᶠ n in Filter.atTop, |(Nat.fib n : ℝ)⁻¹| ≤ 1 :=
    Filter.Eventually.of_forall fun n ↦ by simp [Nat.cast_inv_le_one]
  convert Filter.Tendsto.add_const _ <| bdd_le_mul_tendsto_zero' _ this <|
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one <|
      abs_lt.mpr ⟨Real.neg_one_lt_goldenConj, by linarith [Real.goldenConj_neg]⟩
  simp

/-- The limit of dividing consecutive Fibonacci numbers in reverse order
is the negative conjugate of the golden ratio. -/
theorem tendsto_fib_div_fib_succ_atTop :
    Filter.Tendsto (fun n ↦ (Nat.fib n / Nat.fib (n + 1) : ℝ)) Filter.atTop <| nhds (-ψ) := by
  rw [← Real.inv_goldenRatio, ← funext <| fun n ↦ inv_div ..]
  exact Filter.Tendsto.inv₀ tendsto_fib_succ_div_fib_atTop Real.goldenRatio_ne_zero
