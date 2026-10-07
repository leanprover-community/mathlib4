/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cesàro means of geometrically decaying sequences

For a real sequence `a` with `|a k| ≤ C * r ^ k` and `0 ≤ r < 1`, the Cesàro
means `n⁻¹ * ∑ k < n, a k` tend to zero.  The file gives the explicit rate
bound first (`abs_sum_range_div_le_of_abs_le_geometric`, independently useful
in error estimates) and then the limit statement as an immediate squeeze.

These statements are the analytic engine behind ergodic-theorem arguments for
geometrically contracting Markov kernels: the deviation from a stationary
distribution decays geometrically, so its Cesàro means vanish.  The specific
application should not be needed in the statement, and is not.

TODO (validation, before this leaves draft status):
* confirm the minimal import set by building (`Finset.abs_sum_le_sum_abs`,
  `geom_sum_mul_neg`, `le_div_iff₀` and the `atTop` cast lemmas may have
  moved or been renamed on current master);
* consider the normed-group generalisation `a : ℕ → E` with
  `‖a k‖ ≤ C * r ^ k`, of which this is the `E = ℝ` special case;
* bikeshed names and file placement with a reviewer.
-/

public section

open Filter

/-- **Explicit rate for Cesàro means of a geometrically decaying sequence**:
if `|a k| ≤ C * r ^ k` with `0 ≤ C` and `0 ≤ r < 1`, then for every `n ≥ 1`
the `n`-th Cesàro mean of `a` is bounded by `(C / (1 - r)) * n⁻¹`. -/
theorem abs_sum_range_div_le_of_abs_le_geometric {a : ℕ → ℝ} {C r : ℝ} (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, |a k| ≤ C * r ^ k) {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k| ≤ (C / (1 - r)) * (n : ℝ)⁻¹ := by
  have hden : 0 < 1 - r := by linarith
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  calc |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k|
      = (n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, a k| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |a k| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (le_of_lt (inv_pos.mpr hnpos))
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, C * r ^ k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h k)
          (le_of_lt (inv_pos.mpr hnpos))
    _ = C * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, r ^ k) := by
        simp only [Finset.mul_sum]
        ring_nf
    _ ≤ C * ((n : ℝ)⁻¹ * (1 / (1 - r))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hnpos))
        rw [le_div_iff₀ hden, geom_sum_mul_neg]
        linarith [pow_nonneg hr0 n]
    _ = (C / (1 - r)) * (n : ℝ)⁻¹ := by ring

/-- **Cesàro means of a geometrically decaying sequence tend to zero**: if
`|a k| ≤ C * r ^ k` with `0 ≤ C` and `0 ≤ r < 1`, then
`n⁻¹ * ∑ k < n, a k → 0`, by squeezing with the explicit rate
`(C / (1 - r)) * n⁻¹`. -/
theorem tendsto_sum_range_div_nhds_zero_of_abs_le_geometric {a : ℕ → ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, |a k| ≤ C * r ^ k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ (C / (1 - r)) * (n : ℝ)⁻¹) atTop (nhds 0) := by
    have hninv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := C / (1 - r))).mul hninv
  have hfg : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k| ≤ (C / (1 - r)) * (n : ℝ)⁻¹ :=
    eventually_atTop.2
      ⟨1, fun n hn ↦ abs_sum_range_div_le_of_abs_le_geometric hC hr0 hr1 h hn⟩
  have hzero : Tendsto (fun n : ℕ ↦ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k|)
      atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) hfg hlim
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hzero
