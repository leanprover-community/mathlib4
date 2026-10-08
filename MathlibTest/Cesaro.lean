/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
import Mathlib.Analysis.SpecificLimits.Cesaro

/-!
# Tests and usage examples for Cesàro means of geometric sequences

Worked examples for `Mathlib.Analysis.SpecificLimits.Cesaro`: applying the
explicit-rate bound and the limit lemma to concrete sequences, over `ℝ` and
over a general normed space.
-/

open Finset Filter

section RealExamples

/-- The geometric sequence `a k = r ^ k` satisfies the bound with `C = 1`. -/
example (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * ∑ k ∈ range n, r ^ k| ≤ (1 / (1 - r)) * (n : ℝ)⁻¹ :=
  abs_sum_range_div_le_of_abs_le_geometric zero_le_one hr0 hr1
    (fun k => by rw [abs_of_nonneg (pow_nonneg hr0 k), one_mul]) hn

/-- The Cesàro means of the geometric sequence `r ^ k` tend to zero. -/
example (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, r ^ k) atTop (nhds 0) :=
  tendsto_sum_range_div_nhds_zero_of_abs_le_geometric zero_le_one hr0 hr1
    (fun k => by rw [abs_of_nonneg (pow_nonneg hr0 k), one_mul])

/-- The zero sequence: every Cesàro mean is exactly `0`. -/
example (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ _k ∈ range n, (0 : ℝ)) atTop (nhds 0) :=
  tendsto_sum_range_div_nhds_zero_of_abs_le_geometric zero_le_one hr0 hr1
    (fun _k => by cases _k <;> simp [pow_nonneg hr0])

end RealExamples

section NormedSpaceExamples

/-- In any normed space over `ℝ`: scaling a geometric sequence by a fixed
vector `z` gives `‖r ^ k • z‖ = r ^ k * ‖z‖`, so the bound applies with
`C = ‖z‖`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℝ)⁻¹ • ∑ k ∈ range n, (r ^ k) • z‖ ≤ (‖z‖ / (1 - r)) * (n : ℝ)⁻¹ :=
  norm_sum_range_smul_le_of_norm_le_geometric (norm_nonneg z) hr0 hr1
    (fun k => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 k)]
      exact (mul_comm (r ^ k) ‖z‖).le) hn

/-- The scaled geometric sequence's Cesàro means tend to `0` in norm. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, (r ^ k) • z) atTop (nhds 0) :=
  tendsto_sum_range_smul_nhds_zero_of_norm_le_geometric (norm_nonneg z) hr0 hr1
    (fun k => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 k)]
      exact (mul_comm (r ^ k) ‖z‖).le)

end NormedSpaceExamples
