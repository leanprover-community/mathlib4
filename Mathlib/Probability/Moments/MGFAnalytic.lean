/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.Taylor

/-!
# The moment-generating function is analytic

The moment-generating function `mgf X μ` of a random variable `X` with respect to a measure `μ`
is analytic on the interior of `integrableExpSet X μ`, the interval on which it is defined.

## Main results

* `analyticOn_mgf`: the moment-generating function is analytic on the interior of the interval
  on which it is defined.
* `iteratedDeriv_mgf`: the n-th derivative of the mgf at `t` is `μ[X ^ n * exp (t * X)]`.

* `analyticOn_cgf`: the cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`.

-/

public section


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ}

/-- For `t : ℝ` with `t ∈ interior (integrableExpSet X μ)`, the derivative of the function
`x ↦ μ[X ^ n * exp (x * X)]` at `t` is `μ[X ^ (n + 1) * exp (t * X)]`. -/
lemma hasDerivAt_integral_pow_mul_exp_real (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun t ↦ μ[fun ω ↦ X ω ^ n * exp (t * X ω)])
      μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] t := by
  have h_re_of_mem n t (ht' : t ∈ interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * exp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re, ← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet ?_ n
      simpa using ht'
  have h_re n : ∀ᶠ t' : ℝ in 𝓝 t, (∫ ω, X ω ^ n * Complex.exp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * exp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _), ← h_re_of_mem _ t ht]
  exact (hasDerivAt_integral_pow_mul_exp (by simp [ht]) n).real_of_complex

section DerivMGF

/-- For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`. -/
lemma hasDerivAt_mgf (h : t ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (mgf X μ) (μ[fun ω ↦ X ω * exp (t * X ω)]) t := by
  convert hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp

lemma hasDerivAt_iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (mgf X μ)) μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] t := by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t ↦ μ[fun ω ↦ X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 t, y ∈ interior (integrableExpSet X μ) :=
        isOpen_interior.eventually_mem ht
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp_real ht (n + 1)

/-- For `t ∈ interior (integrableExpSet X μ)`, the n-th derivative of `mgf X μ` at `t` is
`μ[X ^ n * exp (t * X)]`. -/
lemma iteratedDeriv_mgf (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) t = μ[fun ω ↦ X ω ^ n * exp (t * X ω)] := by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

/-- The derivatives of the moment-generating function at zero are the moments. -/
lemma iteratedDeriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (mgf X μ) 0 = μ[X ^ n] := by
  simp [iteratedDeriv_mgf h n]

/-- For `t ∈ interior (integrableExpSet X μ)`, the derivative of `mgf X μ` at `t` is
`μ[X * exp (t * X)]`. -/
lemma deriv_mgf (h : t ∈ interior (integrableExpSet X μ)) :
    deriv (mgf X μ) t = μ[fun ω ↦ X ω * exp (t * X ω)] :=
  (hasDerivAt_mgf h).deriv

lemma deriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) : deriv (mgf X μ) 0 = μ[X] := by
  simp [deriv_mgf h]

end DerivMGF

section AnalyticMGF

/-- The moment-generating function is analytic at every `t ∈ interior (integrableExpSet X μ)`. -/
lemma analyticAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℝ (mgf X μ) t := by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal

lemma analyticOnNhd_mgf : AnalyticOnNhd ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_mgf hx

/-- The moment-generating function is analytic on the interior of the interval on which it is
defined. -/
lemma analyticOn_mgf : AnalyticOn ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_mgf.analyticOn

lemma hasFPowerSeriesAt_mgf (hv : v ∈ interior (integrableExpSet X μ)) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n !)) v := by
  convert (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

lemma differentiableAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    DifferentiableAt ℝ (mgf X μ) t := (analyticAt_mgf ht).differentiableAt

lemma differentiableOn_mgf : DifferentiableOn ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ (differentiableAt_mgf hx).differentiableWithinAt

-- todo: this should be extended to `integrableExpSet X μ`, not only its interior
lemma continuousOn_mgf : ContinuousOn (mgf X μ) (interior (integrableExpSet X μ)) :=
  differentiableOn_mgf.continuousOn

lemma continuous_mgf (h : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Continuous (mgf X μ) := by
  rw [← continuousOn_univ]
  convert continuousOn_mgf
  symm
  rw [interior_eq_univ]
  ext t
  simpa using h t

lemma analyticOnNhd_iteratedDeriv_mgf (n : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) := by
  rw [iteratedDeriv_eq_iterate]
  exact analyticOnNhd_mgf.iterated_deriv n

lemma analyticOn_iteratedDeriv_mgf (n : ℕ) :
    AnalyticOn ℝ (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) :=
  (analyticOnNhd_iteratedDeriv_mgf n).analyticOn

lemma analyticAt_iteratedDeriv_mgf (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    AnalyticAt ℝ (iteratedDeriv n (mgf X μ)) v :=
  analyticOnNhd_iteratedDeriv_mgf n v hv

lemma differentiableAt_iteratedDeriv_mgf (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    DifferentiableAt ℝ (iteratedDeriv n (mgf X μ)) v :=
  (analyticAt_iteratedDeriv_mgf hv n).differentiableAt

end AnalyticMGF

section AnalyticCGF

lemma analyticAt_cgf (h : v ∈ interior (integrableExpSet X μ)) : AnalyticAt ℝ (cgf X μ) v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure]
    exact analyticAt_const
  · exact (analyticAt_mgf h).log <| mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)

lemma analyticOnNhd_cgf : AnalyticOnNhd ℝ (cgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_cgf hx

/-- The cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`. -/
lemma analyticOn_cgf : AnalyticOn ℝ (cgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_cgf.analyticOn

end AnalyticCGF

section DerivCGF

lemma deriv_cgf (h : v ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) v = μ[fun ω ↦ X ω * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure, integral_zero_measure, mgf_zero_measure, div_zero,
      Pi.zero_apply]
    exact deriv_const v 0
  have hv : Integrable (fun ω ↦ exp (v * X ω)) μ := interior_subset (s := integrableExpSet X μ) h
  calc deriv (fun x ↦ log (mgf X μ x)) v
  _ = deriv (mgf X μ) v / mgf X μ v := by
    rw [deriv.log (differentiableAt_mgf h) ((mgf_pos' hμ hv).ne')]
  _ = μ[fun ω ↦ X ω * exp (v * X ω)] / mgf X μ v := by rw [deriv_mgf h]

lemma deriv_cgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) 0 = μ[X] / μ.real Set.univ := by simp [deriv_cgf h]

lemma iteratedDeriv_two_cgf (h : v ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω ↦ (X ω) ^ 2 * exp (v * X ω)] / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  by_cases hμ : μ = 0
  · simp [hμ]
  have h_mem : ∀ᶠ y in 𝓝 v, y ∈ interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_d_cgf : deriv (cgf X μ) =ᶠ[𝓝 v] fun u ↦ μ[fun ω ↦ X ω * exp (u * X ω)] / mgf X μ u := by
    filter_upwards [h_mem] with u hu using deriv_cgf hu
  have h_d_mgf : deriv (mgf X μ) =ᶠ[𝓝 v] fun u ↦ μ[fun ω ↦ X ω * exp (u * X ω)] := by
    filter_upwards [h_mem] with u hu using deriv_mgf hu
  rw [h_d_cgf.deriv_eq]
  calc deriv (fun u ↦ (∫ ω, X ω * exp (u * X ω) ∂μ) / mgf X μ u) v
  _ = (deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (mgf X μ) v) / mgf X μ v ^ 2 := by
    rw [deriv_fun_div]
    · rw [h_d_mgf.symm.differentiableAt_iff, ← iteratedDeriv_one]
      exact differentiableAt_iteratedDeriv_mgf h 1
    · exact differentiableAt_mgf h
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * ∫ ω, X ω * exp (v * X ω) ∂μ) / mgf X μ v ^ 2 := by
    rw [deriv_mgf h]
  _ = deriv (fun u ↦ ∫ ω, X ω * exp (u * X ω) ∂μ) v / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    rw [sub_div]
    congr 1
    · rw [pow_two, div_mul_eq_div_div, mul_div_assoc, div_self, mul_one]
      exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
    · rw [deriv_cgf h]
      ring
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    congr
    convert (hasDerivAt_integral_pow_mul_exp_real h 1).deriv using 1
    simp

lemma iteratedDeriv_two_cgf_eq_integral (h : v ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω ↦ (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [iteratedDeriv_two_cgf h]
  calc (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ - 2 * (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (cgf X μ) v
      + deriv (cgf X μ) v ^ 2 * mgf X μ v) / mgf X μ v := by
    rw [add_div, sub_div, sub_add]
    congr 1
    rw [mul_div_cancel_right₀, deriv_cgf h]
    · ring
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (∫ ω, ((X ω) ^ 2 - 2 * X ω * deriv (cgf X μ) v + deriv (cgf X μ) v ^ 2) * exp (v * X ω) ∂μ)
      / mgf X μ v := by
    congr 1
    simp_rw [add_mul, sub_mul]
    have h_int : Integrable (fun ω ↦ 2 * X ω * deriv (cgf X μ) v * exp (v * X ω)) μ := by
      simp_rw [mul_assoc, mul_comm (deriv (cgf X μ) v)]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc]
      refine Integrable.mul_const ?_ _
      convert integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 1
      simp
    rw [integral_add]
    rotate_left
    · exact (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2).sub h_int
    · exact (interior_subset (s := integrableExpSet X μ) h).const_mul _
    rw [integral_sub (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2) h_int]
    congr
    · rw [← integral_const_mul, ← integral_mul_const]
      congr with ω
      ring
    · rw [integral_const_mul, mgf]
  _ = (∫ ω, (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v := by
    congr with ω
    ring

lemma exists_cgf_eq_iteratedDeriv_two_cgf_mul [IsZeroOrProbabilityMeasure μ] (ht : 0 < t)
    (hc : μ[X] = 0) (hs : Set.Icc 0 t ⊆ interior (integrableExpSet X μ)) :
    ∃ u ∈ Set.Ioo 0 t, cgf X μ t = (iteratedDeriv 2 (cgf X μ) u) * t ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (Set.Icc 0 t) := uniqueDiffOn_Icc ht
  rw [← sub_zero (cgf X μ t)]
  nth_rw 3 [← sub_zero t]
  rw [← Set.uIoo_of_lt ht]
  convert taylor_mean_remainder_lagrange_iteratedDeriv ht.ne ?_
  · have hd : derivWithin (cgf X μ) (Set.Icc 0 t) 0 = 0 := by
      convert (analyticAt_cgf (hs ⟨le_refl 0, le_of_lt ht⟩)).differentiableAt.derivWithin _
      · simpa [hc] using (deriv_cgf_zero (hs ⟨le_refl 0, le_of_lt ht⟩)).symm
      · exact hu 0 ⟨le_refl 0, le_of_lt ht⟩
    simp [hd, Set.uIcc_of_lt ht]
  · rw [Set.uIcc_of_lt ht]
    exact (analyticOn_cgf.mono hs).contDiffOn hu

end DerivCGF

end ProbabilityTheory
