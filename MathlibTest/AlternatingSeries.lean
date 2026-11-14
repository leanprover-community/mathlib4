module

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz

open Filter Finset
open scoped Topology

-- The new result needs convergence, not absolute summability of the coefficients.
example {E : Type*} [Ring E] [LinearOrder E] [IsOrderedRing E]
    [TopologicalSpace E] [OrderClosedTopology E] (f : ℕ → E) (l : E)
    (hf : Antitone f)
    (hl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)) (n : ℕ) :
    |l - ∑ i ∈ range n, (-1) ^ i * f i| ≤ f n :=
  hf.abs_sub_le_alternating_series hl n

-- The old theorem remains source-compatible.
example (f : ℕ → ℝ) (hf : Antitone f) (hs : Summable f) (n : ℕ) :
    |(∑' i, (-1) ^ i * f i) - ∑ i ∈ range n, (-1) ^ i * f i| ≤ f n :=
  alternating_series_error_bound f hf hs n

-- The positive Leibniz coefficients do not satisfy the old API's hypothesis.
example : ¬ Summable (fun n : ℕ ↦ (1 : ℝ) / (2 * n + 1)) := by
  intro hs
  have h : Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) (hs.mul_left 2)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    field_simp
    nlinarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 (by simpa using h))

-- Empty, odd, and even truncations all use the first omitted term.
example : |Real.pi / 4| ≤ 1 := by
  simpa using Real.abs_pi_div_four_sub_sum_le 0

example : |Real.pi / 4 - 1| ≤ 1 / 3 := by
  convert Real.abs_pi_div_four_sub_sum_le 1 using 1 <;> norm_num [sum_range_succ]

example : |Real.pi / 4 - (2 / 3 : ℝ)| ≤ 1 / 5 := by
  convert Real.abs_pi_div_four_sub_sum_le 2 using 1 <;> norm_num [sum_range_succ]
