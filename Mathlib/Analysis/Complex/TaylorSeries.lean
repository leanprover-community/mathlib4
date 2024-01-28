/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Convergence of Taylor series of holomorphic functions

We show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on the open ball of radius `r` around `c` converges to `f` on that open ball;
see `Complex.hasSum_taylorSeries_on_ball` and `Complex.taylorSeries_eq_on_ball` for versions
(in terms of `HasSum` and `tsum`, repsectively) for functions to a complete normed
space over `ℂ`, and `Complex.taylorSeries_eq_on_ball'` for a variant when `f : ℂ → ℂ`.

We also show that the Taylor series of a function `f` that is complex differentiable on
all of `ℂ` converges to  `f` on `ℂ`; see `Complex.hasSum_taylorSeries_of_entire`,
`Complex.taylorSeries_eq_of_entire` and `Complex.taylorSeries_eq_of_entire'`.
-/

namespace Complex

open BigOperators Nat

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma hasSum_taylorSeries_on_ball {f : ℂ → E} ⦃r : NNReal⦄ (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    HasSum (fun n : ℕ ↦ (1 / n ! : ℂ) • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r'
  · obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    lift r' to NNReal using dist_nonneg.trans h₁.le
    exact ⟨r', h₂, pos_of_gt h₁, Metric.mem_ball'.mpr h₁⟩
  have hz' : z - c ∈ EMetric.ball 0 r'
  · rw [Metric.emetric_ball_nnreal]
    exact mem_ball_zero_iff.mpr hzr'
  have H := (hf.mono <| Metric.closedBall_subset_ball hr').hasFPowerSeriesOnBall hr'₀
      |>.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel'_right] at H
  convert H using 4 with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv ℂ n f c).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on theis open ball. -/
lemma taylorSeries_eq_on_ball {f : ℂ → E} ⦃r : NNReal⦄ (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    ∑' n : ℕ, (1 / n ! : ℂ) • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hr hf hz).tsum_eq

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_ball' {f : ℂ → ℂ} ⦃r : NNReal⦄ (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r) :
    ∑' n : ℕ, (1 / n ! : ℂ) * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_ball hr hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma hasSum_taylorSeries_of_entire {f : ℂ → E} (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ ↦ (1 / n ! : ℂ) • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  have hR := lt_add_of_pos_of_le zero_lt_one <| zero_le (⟨‖z - c‖, norm_nonneg _⟩ : NNReal)
  refine hasSum_taylorSeries_on_ball hR hf.differentiableOn ?_
  rw [mem_ball_iff_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mk, lt_add_iff_pos_left]
  exact zero_lt_one

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire {f : ℂ → E} (hf : Differentiable ℂ f) (c z : ℂ) :
    ∑' n : ℕ, (1 / n ! : ℂ) • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire' {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c z : ℂ) :
    ∑' n : ℕ, (1 / n ! : ℂ) * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end Complex
