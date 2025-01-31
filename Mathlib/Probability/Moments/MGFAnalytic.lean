/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The moment generating function is analytic

The moment generating function `mgf X μ` of a random variable `X` with respect to a measure `μ`
is analytic on the interior of `integrableExpSet X μ`, the interval on which it is defined.

## Main results

* `analyticOn_mgf`: the moment generating function is analytic on the interior of the interval
  on which it is defined.
* `iteratedDeriv_mgf`: the n-th derivative of the mgf at `t` is `μ[X ^ n * exp (t * X)]`.

-/


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ}

section Deriv

/-- For `t : ℝ` with `t ∈ interior (integrableExpSet X μ)`, the derivative of the function
`x ↦ μ[X ^ n * rexp (x * X)]` at `t` is `μ[X ^ (n + 1) * rexp (t * X)]`. -/
lemma hasDerivAt_integral_pow_mul_exp_real (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun t ↦ μ[fun ω ↦ X ω ^ n * rexp (t * X ω)])
      μ[fun ω ↦ X ω ^ (n + 1) * rexp (t * X ω)] t := by
  have h_re_of_mem n t (ht' : t ∈ interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * rexp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re, ← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet ?_ n
      simpa using ht'
  have h_re n : ∀ᶠ t' : ℝ in 𝓝 t, (∫ ω, X ω ^ n * Complex.exp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * rexp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _), ← h_re_of_mem _ t ht]
  exact (hasDerivAt_integral_pow_mul_exp (by simp [ht]) n).real_of_complex

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

/-- The derivatives of the moment generating function at zero are the moments. -/
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

end Deriv

section Analytic

/-- The moment generating function is analytic at every `t ∈ interior (integrableExpSet X μ)`. -/
lemma analyticAt_mgf (ht : t ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℝ (mgf X μ) t := by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal

lemma analyticOnNhd_mgf : AnalyticOnNhd ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx ↦ analyticAt_mgf hx

/-- The moment generating function is analytic on the interior of the interval on which it is
defined. -/
lemma analyticOn_mgf : AnalyticOn ℝ (mgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_mgf.analyticOn

lemma hasFPowerSeriesAt_mgf (hv : v ∈ interior (integrableExpSet X μ)) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n !)) v := by
  convert (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

end Analytic

section GeneratingFunctionDerivatives

variable {X : Ω → ℝ}

lemma integrable_expt_bound [IsFiniteMeasure μ] {t a b : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  cases lt_trichotomy t 0 with
  | inr ht => cases ht with
    | inr ht => exact integrable_exp_mul_of_le t b ht.le hX (h.mono fun ω h ↦ h.2)
    | inl ht => rw [ht]; simp only [zero_mul, exp_zero, integrable_const]
  | inl ht =>
    rw [(by ext ω; rw [(by ring : - t * (- X ω) = t * X ω)] :
      (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (- t * (- X ω))))]
    apply integrable_exp_mul_of_le (-t) _ _ hX.neg
    · filter_upwards [h] with ω h using neg_le_neg h.1
    · linarith

lemma tilt_var_bound [IsProbabilityMeasure μ] (a b t : ℝ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEMeasurable X μ) :
    variance X (μ.tilted (fun ω ↦ t * X ω)) ≤ ((b - a) / 2) ^ 2 := by
  have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
    isProbabilityMeasure_tilted (integrable_expt_bound hX h)
  exact variance_le_sq_of_bounded
    ((tilted_absolutelyContinuous μ fun ω ↦ t * X ω) h)
    (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))

lemma integrableExpSet_eq_univ_of_mem_Icc [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    integrableExpSet X μ = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact integrable_expt_bound hX h

theorem integral_tilted' [IsFiniteMeasure μ] (t : ℝ) (f : ℝ → ℝ) :
    (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ f (X ω)] =
    (μ[fun ω ↦ rexp (t * X ω) * f (X ω)]) / mgf X μ t := by
  rw [MeasureTheory.integral_tilted, ← integral_div]
  simp only [smul_eq_mul, mgf]
  congr with ω
  ring

/-! ### Derivatives of cumulant-/

/-- First derivative of cumulant `cgf X μ f`.
It can be described by exponential tilting.-/
theorem cgf_deriv_one [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (t : ℝ) :
    HasDerivAt (cgf X μ) ((μ.tilted (fun ω ↦ t * X ω))[X]) t := by
  have r0 : ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]) =
      μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted' t id
  simp only [id_eq] at r0
  rw [r0]
  apply HasDerivAt.log ?_ (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'
  convert hasDerivAt_mgf _ using 1
  · simp_rw [mul_comm]
  · simp [integrableExpSet_eq_univ_of_mem_Icc _ _ hX h]

/-- Second derivative of cumulant `cgf X μ f`-/
theorem cgf_deriv_two [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X];
    let g'' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X ^ 2] - (μ.tilted (fun ω ↦ t * X ω))[X] ^ 2;
    ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
  intro g' g'' t
  have r0 : (fun t ↦ ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)])) =
    fun t ↦ μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] := by
    ext t
    exact integral_tilted' t id
  have r01 : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]  =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted' t id
  have r0' : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (fun s ↦ s ^ 2) (X ω)] =
    μ[fun ω ↦ rexp (t * X ω) * (fun s ↦ s ^ 2) (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted' t (fun x ↦ x ^ 2)
  simp only [id_eq] at r0 r0' r01
  dsimp [g', g'']
  rw [r0, r0', r01]
  field_simp
  have p : ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) / μ[fun ω ↦ rexp (t * X ω)]) =
  ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * (μ[fun ω ↦ rexp (t * X ω)])) /
  ((μ[fun ω ↦ rexp (t * X ω)]) * (μ[fun ω ↦ rexp (t * X ω)])) := by
    apply Eq.symm (mul_div_mul_right (∫ ω, rexp (t * X ω) * X ω ^ 2 ∂μ)
    (μ[fun ω ↦ rexp (t * X ω)]) _)
    exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'
  rw [p, Eq.symm (pow_two (∫ ω, rexp (t * X ω) ∂μ))]
  have p'' : (((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) *
    (μ[fun ω ↦ rexp (t * X ω)])) / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2 -
  (μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2 / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2) =
  ((μ[fun ω ↦ exp (t * (X ω)) * (X ω) ^ 2] *
    mgf X μ t) -
    (μ[fun ω ↦ exp (t * (X ω)) * X ω] * μ[fun ω ↦ exp (t * (X ω)) * X ω])) /
    (mgf X μ t ^ 2) := by
    rw [Eq.symm (pow_two (∫ ω, (fun ω ↦ rexp (t * X ω) * X ω) ω ∂μ))]
    exact
      div_sub_div_same ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * μ[fun ω ↦ rexp (t * X ω)])
        ((μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2) ((μ[fun ω ↦ rexp (t * X ω)]) ^ 2)
  rw [p'']
  apply HasDerivAt.div
  · set c := max ‖a‖ ‖b‖
    convert hasDerivAt_integral_pow_mul_exp_real (X := X) (μ := μ) ?_ 1 using 1
    · simp only [pow_one, g'', g']
      simp_rw [mul_comm]
    · simp only [Nat.reduceAdd, g'', g']
      simp_rw [mul_comm]
    · simp [integrableExpSet_eq_univ_of_mem_Icc _ _ hX h]
  · convert hasDerivAt_integral_pow_mul_exp_real (X := X) (μ := μ) ?_ 0 using 1
    · simp
    · simp only [zero_add, pow_one, g'', g']
      simp_rw [mul_comm]
    · simp [integrableExpSet_eq_univ_of_mem_Icc _ _ hX h]
  · exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'

theorem cgf_zero_deriv [IsProbabilityMeasure μ] {X : Ω → ℝ} (h0 : μ[X] = 0) :
    let f' := fun t ↦ ∫ (x : Ω), X x ∂Measure.tilted μ fun ω ↦ t * X ω;
  f' 0 = 0 := by
  simp only [zero_mul, tilted_const', measure_univ, inv_one, one_smul]
  exact h0

end GeneratingFunctionDerivatives

end ProbabilityTheory
