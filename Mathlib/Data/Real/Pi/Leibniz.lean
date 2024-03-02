/-
Copyright (c) 2020 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

#align_import data.real.pi.leibniz from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-! ### Leibniz's series for `π` -/

namespace Real

open Filter Finset

open scoped BigOperators Topology

/-- **Leibniz's series for `π`**. The alternating sum of odd number reciprocals is `π / 4`.

Note that this is a conditionally rather than absolutely convergent series. The main tool that
this proof uses is Abel's limit theorem, which allows us to extend the Maclaurin series of
`arctan x`, which has radius of convergence 1, to `x = 1`. -/
theorem tendsto_sum_pi_div_four :
    Tendsto (fun k => ∑ i in range k, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) := by
  -- The series is alternating with terms of decreasing magnitude, so it converges to _some_ limit
  obtain ⟨l, h⟩ :
      ∃ l, Tendsto (fun n ↦ ∑ i in range n, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 l) := by
    apply (antitone_iff_forall_lt.mpr
      (fun _ _ _ ↦ by dsimp; gcongr)).tendsto_alternating_series_of_tendsto_zero
      (Tendsto.inv_tendsto_atTop (tendsto_atTop_add_const_right _ _ _))
    exact tendsto_nat_cast_atTop_atTop.const_mul_atTop zero_lt_two
  -- Abel's limit theorem states that the corresponding power series has the same limit as `x → 1⁻`
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- Massage the expression to get `x ^ (2 * n + 1)` in the tsum rather than `x ^ n`...
  have q : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
    simp_rw [Metric.tendsto_nhdsWithin_nhdsWithin, Set.mem_Iio, sq_lt_one_iff_abs_lt_one]
    intro ε hε
    use min 1 (ε / 2), by positivity
    intro x lb dx
    rw [dist_eq, lt_min_iff, abs_sub_lt_iff] at dx
    obtain ⟨⟨_, ub⟩, t⟩ := dx
    replace ub : 0 < x := by linarith only [ub]
    have a : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
    refine' ⟨a, _⟩
    rw [dist_eq, show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, abs_mul, show ε = 2 * (ε / 2) by ring]
    gcongr
    exact (abs_add_le x 1).trans_lt (by rw [← one_add_one_eq_two, abs_one]; gcongr)
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := tendsto_nhdsWithin_of_tendsto_nhds fun _ a ↦ a
  replace abel := (abel.comp q).mul m
  rw [mul_one] at abel
  -- ...so that we can replace the tsum with the real arctangent function
  replace abel : Tendsto arctan (𝓝[<] 1) (𝓝 l) := by
    apply abel.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 2, zero_lt_two
    intro y hy1 hy2
    rw [dist_eq, abs_sub_lt_iff] at hy1
    rw [Set.mem_Iio] at hy2
    have ny : ‖y‖ < 1 := by rw [norm_eq_abs, abs_lt]; constructor <;> linarith
    rw [← (hasSum_arctan ny).tsum_eq, Function.comp_apply, ← tsum_mul_right]
    congr with n
    rw [mul_assoc, ← pow_mul, ← pow_succ', div_mul_eq_mul_div]
    norm_cast
  -- But `arctan` is continuous everywhere, so the limit is `arctan 1 = π / 4`
  rwa [tendsto_nhds_unique abel ((continuous_arctan.tendsto 1).mono_left m), arctan_one] at h
#align real.tendsto_sum_pi_div_four Real.tendsto_sum_pi_div_four

end Real
