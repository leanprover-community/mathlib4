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

There are corresponding statements for `EMEtric.ball`s; see
`Complex.hasSum_taylorSeries_on_emetric_ball`, `Complex.taylorSeries_eq_on_emetric_ball`
and `Complex.taylorSeries_eq_on_ball'`.

We also show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on all of `ℂ` converges to `f` on `ℂ`;
see `Complex.hasSum_taylorSeries_of_entire`, `Complex.taylorSeries_eq_of_entire` and
`Complex.taylorSeries_eq_of_entire'`.
-/

namespace Complex

open BigOperators Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] ⦃f : ℂ → E⦄

section ball

variable ⦃c : ℂ⦄ ⦃r : ℝ⦄ (hf : DifferentiableOn ℂ f (Metric.ball c r))
variable ⦃z : ℂ⦄ (hz : z ∈ Metric.ball c r)

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma hasSum_taylorSeries_on_ball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r'
  · obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
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
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_ball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hf hz).tsum_eq

/-- A function that is complex differentiable on the open ball of radius `r` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_ball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end ball

section emetric

variable ⦃c : ℂ⦄ ⦃r : ENNReal⦄ (hf : DifferentiableOn ℂ f (EMetric.ball c r))
variable ⦃z : ℂ⦄ (hz : z ∈ EMetric.ball c r)

/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma hasSum_taylorSeries_on_emetric_ball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hzr', hr'⟩ := exists_between (EMetric.mem_ball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← EMetric.mem_ball', Metric.emetric_ball_nnreal] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.emetric_ball_nnreal]
  exact hf.mono <| EMetric.ball_subset_ball hr'.le

/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_emetric_ball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_emetric_ball hf hz).tsum_eq

/-- A function that is complex differentiable on the open ball of radius `r ≤ ∞` around `c`
is given by evaluating its Taylor series at `c` on this open ball. -/
lemma taylorSeries_eq_on_emetric_ball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (EMetric.ball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_emetric_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end emetric

section entire

variable ⦃f : ℂ → E⦄ (hf : Differentiable ℂ f) (c z : ℂ)

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma hasSum_taylorSeries_of_entire :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  hasSum_taylorSeries_on_emetric_ball hf.differentiableOn <| EMetric.mem_ball.mpr <|
    edist_lt_top ..

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq

/-- A function that is complex differentiable on the complex plane is given by evaluating
its Taylor series at any point `c`. -/
lemma taylorSeries_eq_of_entire' {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]

end entire

end Complex
