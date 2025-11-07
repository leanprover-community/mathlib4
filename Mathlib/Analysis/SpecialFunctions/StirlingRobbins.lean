/-
Copyright (c) 2024 Ashton Jenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashton Jenson
-/
import Mathlib.Analysis.SpecialFunctions.Stirling

open scoped BigOperators Nat

namespace Stirling

/-!
# Robbins' Sharp Stepwise Bound for Stirling Sequence

This file proves the sharp Robbins bound for successive differences in the
logarithm of the Stirling sequence:

$$|\log(\mathrm{stirlingSeq}(k+1)) - \log(\mathrm{stirlingSeq}(k))|
  \le \frac{1}{12k(k+1)}$$

This improves upon Mathlib's bound of $1/(4k^2)$ given in
`log_stirlingSeq_sub_log_stirlingSeq_succ`, and represents work that
Mathlib documentation notes as "not yet formalized."

## Main Result

* `log_stirlingSeq_diff_le`: The sharp Robbins bound

## References

* <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Stirling.html>
* `log_stirlingSeq_sub_log_stirlingSeq_succ` provides the weaker bound

## Tags

stirling, factorial, robbins, bounds
-/

/-! ### Helper lemmas -/

/-- For `k ≥ 1`, the ratio `1/(2k+1)` satisfies $(1/(2k+1))^2 < 1$. -/
lemma ratio_sq_lt_one {k : ℕ} (hk : 1 ≤ k) :
    ((1 : ℝ) / (2 * k + 1)) ^ 2 < 1 := by
  rw [div_pow, one_pow, div_lt_one (by positivity : 0 < (2 * (k : ℝ) + 1) ^ 2)]
  have : (3 : ℝ) ≤ 2 * k + 1 := by norm_cast; omega
  nlinarith [sq_nonneg (2 * (k : ℝ) + 1 - 3)]

/-- The Stirling series is summable and bounded termwise by a geometric series. -/
lemma stirling_series_summable_and_bounded {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun j : ℕ =>
      (1 : ℝ) / (2 * (j + 1) + 1) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1)) ∧
    ∀ (j : ℕ), (1 : ℝ) / (2 * (j + 1) + 1) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1)
      ≤ (1 / 3) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1) := by
  set r := ((1 : ℝ) / (2 * k + 1)) ^ 2
  constructor
  · -- Summability: use comparison with geometric series
    have h_summable : Summable (fun j : ℕ => r ^ (j + 1) / (2 * j + 3)) := by
      apply Summable.of_nonneg_of_le
      · intro j
        positivity
      · intro j
        apply div_le_self
        · positivity
        · linarith
      · apply Summable.comp_injective
        · exact summable_geometric_of_lt_one (by positivity) (ratio_sq_lt_one hk)
        · exact fun {a b} => Nat.succ.inj
    convert h_summable using 2
    ring
  · -- Termwise bound: coefficient 1/(2j+3) ≤ 1/3 for all j ≥ 0
    intro j
    apply mul_le_mul_of_nonneg_right
    · have : 2 * (j + 1) + 1 ≥ 3 := by linarith [Nat.zero_le j]
      gcongr
      norm_cast
    · positivity

/-- The Stirling series is bounded by a geometric series. -/
lemma stirling_series_le_geom {k : ℕ} (hk : 1 ≤ k) :
    (∑' j : ℕ, (1 : ℝ) / (2 * (j + 1) + 1) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1))
      ≤ (∑' j : ℕ, (1 / 3 : ℝ) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1)) := by
  obtain ⟨h_summ, h_bound⟩ := stirling_series_summable_and_bounded hk
  have h_geom : Summable (fun j : ℕ =>
      (1 / 3 : ℝ) * ((1 / (2 * k + 1)) ^ 2) ^ (j + 1)) := by
    set r := ((1 : ℝ) / (2 * k + 1)) ^ 2
    convert (summable_geometric_of_lt_one (by positivity)
      (ratio_sq_lt_one hk)).mul_left r |>.mul_left (1/3) using 2
    ring
  exact Summable.tsum_le_tsum h_bound h_summ h_geom

/-- Algebraic identity: $(1/3) \cdot [r/(1-r)] = 1/(12k(k+1))$
where $r = (1/(2k+1))^2$. -/
lemma geom_ratio_identity {k : ℕ} (hk : 1 ≤ k) :
    (1 / 3 : ℝ) * (((1 / (2 * k + 1)) ^ 2) / (1 - (1 / (2 * k + 1)) ^ 2))
      = 1 / (12 * k * (k + 1)) := by
  have h_nz1 : (2 * (k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have h_nz2 : 4 * (k : ℝ) * (k + 1) ≠ 0 := by positivity
  have h_nz3 : 12 * (k : ℝ) * (k + 1) ≠ 0 := by positivity
  -- (2k+1)² - 1 = 4k(k+1)
  have one_sub_r : 1 - ((1 : ℝ) / (2 * k + 1)) ^ 2 =
      (4 * k * (k + 1)) / ((2 * k + 1) ^ 2) := by
    field_simp
    ring
  rw [one_sub_r]
  field_simp
  ring

/-- The sequence $\log(\mathrm{stirlingSeq}(n))$ is decreasing for $n \ge 1$. -/
lemma log_stirlingSeq_diff_nonpos {k : ℕ} (hk : 1 ≤ k) :
    Real.log (stirlingSeq (k + 1)) - Real.log (stirlingSeq k) ≤ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h_anti : stirlingSeq (n + 2) ≤ stirlingSeq (n + 1) :=
    stirlingSeq'_antitone (Nat.le_succ n)
  linarith [Real.log_le_log (stirlingSeq'_pos (n + 1)) h_anti]

/-- The series expansion from `log_stirlingSeq_diff_hasSum` applies to our indices. -/
lemma stirling_series_hasSum {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun j : ℕ => (1 : ℝ) / (2 * (j + 1) + 1) *
      ((1 / (2 * k + 1)) ^ 2) ^ (j + 1))
      (Real.log (stirlingSeq k) - Real.log (stirlingSeq (k + 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  convert log_stirlingSeq_diff_hasSum m using 1
  ext j
  simp

/-! ### Main result -/

/-- **Robbins' sharp stepwise bound** for the Stirling sequence:
The absolute difference of consecutive log values is bounded by $1/(12k(k+1))$. -/
theorem log_stirlingSeq_diff_le {k : ℕ} (hk : 1 ≤ k) :
    |Real.log (stirlingSeq (k + 1)) - Real.log (stirlingSeq k)|
      ≤ (1 : ℝ) / (12 * k * (k + 1)) := by
  -- log(stirlingSeq) is decreasing, therefore the difference is non-positive
  rw [abs_of_nonpos (log_stirlingSeq_diff_nonpos hk)]
  have : -(Real.log (stirlingSeq (k + 1)) - Real.log (stirlingSeq k))
      = Real.log (stirlingSeq k) - Real.log (stirlingSeq (k + 1)) := by ring
  rw [this, ← (stirling_series_hasSum hk).tsum_eq]
  set r := ((1 : ℝ) / (2 * k + 1)) ^ 2
  -- Bound the series: sum of coefficients * r^j ≤ (1/3) * geometric series
  calc (∑' j : ℕ, (1 : ℝ) / (2 * (j + 1) + 1) * r ^ (j + 1))
      ≤ (∑' j : ℕ, (1 / 3 : ℝ) * r ^ (j + 1)) := stirling_series_le_geom hk
    _ = (1 / 3) * (∑' j : ℕ, r ^ (j + 1)) := by rw [tsum_mul_left]
    _ = (1 / 3) * (r * ∑' j : ℕ, r ^ j) := by
        congr 1
        rw [← tsum_mul_left]
        exact tsum_congr fun _ => by ring
    _ = (1 / 3) * (r / (1 - r)) := by
        -- Evaluate geometric series: ∑ r^j = 1/(1-r)
        rw [tsum_geometric_of_lt_one (by positivity) (ratio_sq_lt_one hk)]
        ring
    _ = (1 : ℝ) / (12 * k * (k + 1)) := geom_ratio_identity hk

end Stirling
