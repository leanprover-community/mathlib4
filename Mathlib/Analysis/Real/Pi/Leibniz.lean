/-
Copyright (c) 2020 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered

/-! ### Leibniz's series for `π` -/

public section

namespace Real

open Filter Finset

open scoped Topology

/-- **Leibniz's series for `π`**. The alternating sum of odd number reciprocals is `π / 4`,
proved by using Abel's limit theorem to extend the Maclaurin series of `arctan` to 1. -/
theorem tendsto_sum_pi_div_four :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) := by
  -- The series is alternating with terms of decreasing magnitude, so it converges to some limit
  obtain ⟨l, h⟩ :
      ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ ↦ by gcongr
    · apply Tendsto.inv_tendsto_atTop; apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two
  -- Abel's limit theorem states that the corresponding power series has the same limit as `x → 1⁻`
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- Massage the expression to get `x ^ (2 * n + 1)` in the tsum rather than `x ^ n`...
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := tendsto_nhdsWithin_of_tendsto_nhds fun _ a ↦ a
  have q : Tendsto (fun x : ℝ ↦ x ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · nth_rw 3 [← one_pow 2]
      exact Tendsto.pow ‹_› _
    · rw [eventually_iff_exists_mem]
      use Set.Ioo (-1) 1
      exact ⟨Ioo_mem_nhdsLT <| by simp,
        fun _ _ ↦ by rwa [Set.mem_Iio, sq_lt_one_iff_abs_lt_one, abs_lt, ← Set.mem_Ioo]⟩
  replace abel := (abel.comp q).mul m
  rw [mul_one] at abel
  -- ...so that we can replace the tsum with the real arctangent function
  replace abel : Tendsto arctan (𝓝[<] 1) (𝓝 l) := by
    apply abel.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1, zero_lt_one
    intro y hy1 hy2
    rw [dist_eq, abs_sub_lt_iff] at hy1
    rw [Set.mem_Iio] at hy2
    have ny : ‖y‖ < 1 := by rw [norm_eq_abs, abs_lt]; constructor <;> linarith
    rw [← (hasSum_arctan ny).tsum_eq, Function.comp_apply, ← tsum_mul_right]
    simp_rw [mul_assoc, ← pow_mul, ← pow_succ, div_mul_eq_mul_div]
    norm_cast
  -- But `arctan` is continuous everywhere, so the limit is `arctan 1 = π / 4`
  rwa [tendsto_nhds_unique abel ((continuous_arctan.tendsto 1).mono_left m), arctan_one] at h

end Real
