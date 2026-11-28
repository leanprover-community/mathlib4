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

References: the Cesàro mean goes back to U. Cesàro, *Sopra la serie di
funzioni*, Atti dell'Accad. Sci. Fis. Mat. (Catania) (1889); the standard
treatment is G. H. Hardy, *Divergent Series* (1949), ch. I.  The
orbit-average framing of the last example follows A. Tserunyan,
*A descriptive set theorist's proof of the pointwise ergodic theorem*,
arXiv:1805.07365, which reduces Birkhoff's theorem [Birkhoff 1931, PNAS 17]
to a tiling problem: tightly tile each orbit by intervals whose averages
are tightly controlled.
-/

open Finset Filter

section RealExamples

/-- The real-valued explicit-rate bound (worked out here from the normed-space
primary; cf. Hardy, *Divergent Series*, ch. I, for the classical form). -/
example (a : ℕ → ℝ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, |a k| ≤ C * r ^ k) {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * ∑ k ∈ range n, a k| ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
  have h' : ∀ k : ℕ, ‖a k‖ ≤ C * r ^ k := fun k => by
    rw [Real.norm_eq_abs]
    exact h k
  have hgen := norm_sum_range_smul_le_of_norm_le_geometric hC hr0 hr1 h' hn
  rwa [Real.norm_eq_abs, smul_eq_mul] at hgen

/-- The geometric sequence `a k = r ^ k` satisfies the bound with `C = 1`. -/
example (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * ∑ k ∈ range n, r ^ k| ≤ (1 / (1 - r)) * (n : ℝ)⁻¹ := by
  have h' : ∀ k : ℕ, ‖(r ^ k : ℝ)‖ ≤ 1 * r ^ k := fun k => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 k), one_mul]
  have hgen := norm_sum_range_smul_le_of_norm_le_geometric zero_le_one hr0 hr1 h' hn
  rwa [Real.norm_eq_abs, smul_eq_mul] at hgen

/-- The real-valued limit (worked out here from the normed-space primary). -/
example (a : ℕ → ℝ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, |a k| ≤ C * r ^ k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, a k) atTop (nhds 0) := by
  have h' : ∀ k : ℕ, ‖a k‖ ≤ C * r ^ k := fun k => by
    rw [Real.norm_eq_abs]
    exact h k
  have hgen := tendsto_sum_range_smul_nhds_zero_of_norm_le_geometric hC hr0 hr1 h'
  exact hgen.congr' (by filter_upwards with n; simp [smul_eq_mul])

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

/-- Orbit-average framing (Tserunyan, arXiv:1805.07365): the constant
observable tiles the orbit with uniform tiles, so every Cesàro mean is
exactly `c` - the uniform-tile case of the tiling lemma that underlies the
pointwise ergodic theorem [Birkhoff 1931, PNAS 17]. -/
example (c : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ _k ∈ range n, c) atTop (nhds c) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  field_simp
  simp [Finset.sum_const, mul_comm]

end NormedSpaceExamples
