/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a nonnegative, strictly convex function on [0,∞), with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff `llr μ ν` is integrable
  with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal`.

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

/-- The function `x : ℝ ↦ x * log x + 1 - x`.
The Kullback-Leibler divergence is an f-divergence for this function. -/
noncomputable abbrev klFun (x : ℝ) : ℝ := x * log x + 1 - x

lemma klFun_one : klFun 1 = 0 := by simp

/-- `klFun` is strictly convex on [0,∞). -/
lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun := by
  unfold klFun
  simp_rw [add_sub_assoc]
  refine strictConvexOn_mul_log.add_convexOn ?_
  exact (convexOn_const _ (convex_Ici _)).sub (concaveOn_id (convex_Ici _))

/-- `klFun` is convex on [0,∞). -/
lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

/-- `klFun` is continuous. -/
@[continuity, fun_prop]
lemma continuous_klFun : Continuous klFun := by fun_prop

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

/-- The derivative of `klFun` at `x ≠ 0` is `log x`. -/
@[simp]
lemma deriv_klFun (hx : x ≠ 0) : deriv klFun x = log x := (hasDerivAt_klFun hx).deriv

/-- The right derivative of `klFun` at `x ≠ 0` is `log x`. -/
@[simp]
lemma rightDeriv_klFun (hx : x ≠ 0) : derivWithin klFun (Ioi x) x = log x :=
  (hasDerivAt_klFun hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- The left derivative of `klFun` at `x ≠ 0` is `log x`. -/
@[simp]
lemma leftDeriv_klFun (hx : x ≠ 0) : derivWithin klFun (Iio x) x = log x :=
  (hasDerivAt_klFun hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp

lemma leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0 := by simp

lemma rightDeriv_klFun_eventually_eq : (fun x ↦ derivWithin klFun (Ioi x) x) =ᶠ[atTop] log := by
  filter_upwards [eventually_ne_atTop 0] with x hx
  rw [rightDeriv_klFun hx]

lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x ↦ derivWithin klFun (Ioi x) x) atTop atTop := by
  rw [tendsto_congr' rightDeriv_klFun_eventually_eq]
  exact tendsto_log_atTop

end Derivatives

/-- The function `klFun` is nonnegative on `[0,∞)`. -/
lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [← klFun_one]
    refine ConvexOn.ge_of_rightDeriv_eq_zero (S := Ioi 0) ?_ (by simp) (by simp)  hx
    exact convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy ↦ h ▸ klFun_nonneg hy)
    (isMinOn_iff.mpr fun y hy ↦ klFun_one ▸ klFun_nonneg hy) hx (zero_le_one' ℝ)

lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x ↦ x * (log x - 1) + 1) := by ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine Tendsto.atTop_mul_atTop ?_ ?_
  · exact fun _ s ↦ s
  · exact tendsto_log_atTop.atTop_add tendsto_const_nhds

/-- For two finite measures `μ ≪ ν`, the function `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable
with respect to `ν` iff `llr μ ν` is integrable with respect to `μ`. -/
lemma integrable_klFun_rnDeriv_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by
  suffices Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert this using 3 with x
    rw [klFun, add_sub_assoc]
  rw [integrable_add_iff_integrable_left']
  · rw [integrable_rnDeriv_mul_log_iff hμν]
  · exact (integrable_const _).sub Measure.integrable_toReal_rnDeriv

lemma integral_klFun_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
    mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact integrable_const _
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact Measure.integrable_toReal_rnDeriv

end ProbabilityTheory
