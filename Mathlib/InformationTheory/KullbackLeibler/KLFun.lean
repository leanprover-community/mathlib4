/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`. That is, the Kullback-Leibler divergence is an integral
of `klFun` composed with a Radon-Nikodym derivative.

For probability measures, any function `f` that differs from `klFun` by an affine function of the
form `x ↦ a * (x - 1)` would give the same value for the integral
`∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
However, `klFun` is the particular choice among those that satisfies `klFun 1 = 0` and
`deriv klFun 1 = 0`, which ensures that desirable properties of the Kullback-Leibler divergence
extend to other finite measures: it is nonnegative and zero iff the two measures are equal.

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a continuous nonnegative, strictly convex function on [0,∞), with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff the log-likelihood ratio
  `llr μ ν` is integrable with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`.

-/

open Real MeasureTheory Filter Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

/-- The function `x : ℝ ↦ x * log x + 1 - x`.
The Kullback-Leibler divergence is an f-divergence for this function. -/
noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x

lemma klFun_apply (x : ℝ) : klFun x = x * log x + 1 - x := rfl

lemma klFun_zero : klFun 0 = 1 := by simp [klFun]

lemma klFun_one : klFun 1 = 0 := by simp [klFun]

/-- `klFun` is strictly convex on [0,∞). -/
lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

/-- `klFun` is convex on [0,∞). -/
lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

/-- `klFun` is convex on (0,∞).
This is an often useful consequence of `convexOn_klFun`, which states convexity on [0, ∞). -/
lemma convexOn_Ioi_klFun : ConvexOn ℝ (Ioi 0) klFun :=
  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

/-- `klFun` is continuous. -/
@[continuity, fun_prop]
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop

/-- `klFun` is measurable. -/
@[measurability, fun_prop]
lemma measurable_klFun : Measurable klFun := continuous_klFun.measurable

/-- `klFun` is strongly measurable. -/
@[measurability]
lemma stronglyMeasurable_klFun : StronglyMeasurable klFun := measurable_klFun.stronglyMeasurable

section Derivatives

/-- The derivative of `klFun` at `x ≠ 0` is `log x`. -/
lemma hasDerivAt_klFun (hx : x ≠ 0) : HasDerivAt klFun (log x) x := by
  convert ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

lemma not_differentiableAt_klFun_zero : ¬ DifferentiableAt ℝ klFun 0 := by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

/-- The derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `deriv` in that case is 0. -/
@[simp]
lemma deriv_klFun : deriv klFun = log := by
  ext x
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact deriv_zero_of_not_differentiableAt not_differentiableAt_klFun_zero
  · exact (hasDerivAt_klFun h0).deriv

lemma not_differentiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt ℝ klFun (Ioi 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsGT_zero

lemma not_differentiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt ℝ klFun (Iio 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsLT_zero

/-- The right derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
lemma rightDeriv_klFun : derivWithin klFun (Ioi x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Ioi_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- The left derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
lemma leftDeriv_klFun : derivWithin klFun (Iio x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Iio_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp

lemma leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0 := by simp

lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x ↦ derivWithin klFun (Ioi x) x) atTop atTop := by
  simp only [rightDeriv_klFun]
  exact tendsto_log_atTop

end Derivatives

lemma isMinOn_klFun : IsMinOn klFun (Ici 0) 1 :=
  convexOn_klFun.isMinOn_of_rightDeriv_eq_zero (by simp) (by simp)

/-- The function `klFun` is nonnegative on `[0,∞)`. -/
lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := klFun_one ▸ isMinOn_klFun hx

lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy ↦ h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' ℝ)

lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x ↦ x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

section Integral

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- For two finite measures `μ ≪ ν`, the function `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable
with respect to `ν` iff `llr μ ν` is integrable with respect to `μ`. -/
lemma integrable_klFun_rnDeriv_iff (hμν : μ ≪ ν) :
    Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by
  suffices Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert this using 3 with x
    rw [klFun, add_sub_assoc]
  rw [integrable_add_iff_integrable_left', integrable_rnDeriv_mul_log_iff hμν]
  fun_prop

lemma integral_klFun_rnDeriv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  unfold klFun
  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
    mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop

end Integral

end InformationTheory
