/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Real Set Finset

open scoped Real Interval

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (c d : ℝ)

@[simp]
theorem _root_.IntervalIntegrable.log (hf : ContinuousOn f [[a, b]])
    (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable

/--
See `intervalIntegrable_log'` for a version without any hypothesis on the interval, but assuming the
measure is the volume.
-/
@[simp]
theorem intervalIntegrable_log (h : (0 : ℝ) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

/--
The real logarithm is interval integrable (with respect to the volume measure) on every interval.
See `intervalIntegrable_log` for a version applying to any locally finite measure, but with an
additional hypothesis on the interval.
-/
@[simp]
theorem intervalIntegrable_log' : IntervalIntegrable log volume a b := by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg (g := fun x ↦ -(x * log x - x))
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro s ⟨hs, _⟩
      norm_num at *
      simpa using (hasDerivAt_id s).sub (hasDerivAt_mul_log hs.ne.symm)
    · intro s ⟨hs₁, hs₂⟩
      norm_num at *
      exact (log_nonpos_iff hs₁.le).mpr hs₂.le
  · -- Show integrability on [1…t] by continuity
    apply ContinuousOn.intervalIntegrable
    apply Real.continuousOn_log.mono
    apply Set.not_mem_uIcc_of_lt zero_lt_one at hx
    simpa

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
@[simp]
theorem intervalIntegrable_log_norm_meromorphicOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i)), (by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_order_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.order_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply _root_.intervalIntegrable_const_iff.2
    tauto

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f⁺ ·‖` is interval integrable on this
interval.
-/
@[simp]
theorem intervalIntegrable_posLog_norm_meromorphicOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply (intervalIntegrable_log_norm_meromorphicOn hf).const_mul
  · apply (intervalIntegrable_log_norm_meromorphicOn hf).abs.const_mul

/--
If `f` is real-meromorphic on a compact interval, then `log ∘ f` is interval integrable on this
interval.
-/
@[simp]
theorem _root_.MeromorphicOn.intervalIntegrable_log {f : ℝ → ℝ}
    (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ∘ f) volume a b := by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact intervalIntegrable_log_norm_meromorphicOn hf

@[simp]
theorem intervalIntegrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.intervalIntegrable a b

@[simp]
theorem intervalIntegrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.intervalIntegrable a b

/--
The function `log ∘ sin` is interval integrable over every interval.
-/
@[simp]
theorem intervalIntegrable_log_sin {a b : ℝ} :
    IntervalIntegrable (log ∘ sin) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log
  apply AnalyticOnNhd.meromorphicOn
  apply analyticOnNhd_sin.mono
  tauto

/-!
# Circle Integrability Properties of Meromorphic Functions

If `f` is meromorphic on the complex plane, we show that the function `log ‖f ·‖` and `log⁺ ‖f ·‖`
are circle integrable.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {c : ℂ} {R : ℝ} {f : ℂ → E}

open Filter MeromorphicOn Metric Real

/--
If `f` is meromorphic on a circle in the complex plane, then `log ‖f ·‖` is circle integrable over
that circle.
-/
@[simp]
theorem circleIntegrable_log_norm_meromorphicOn (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log ‖f ·‖) c R := by
  by_cases t₀ : ∀ u : (sphere c |R|), (hf u u.2).order ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      unfold CircleIntegrable
      apply IntervalIntegrable.const_mul
      apply intervalIntegral.intervalIntegrable_log_norm_meromorphicOn
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq, norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_order_ne_top_iff_forall (isConnected_sphere (by simp) c (abs_nonneg R))] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.order_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

/--
If `f` is meromorphic on a circle in the complex plane, then `log⁺ ‖f ·‖` is circle integrable over
that circle.
-/
@[simp]
theorem circleIntegrable_posLog_norm_meromorphicOn (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply (circleIntegrable_log_norm_meromorphicOn hf).const_mul
  · apply IntervalIntegrable.const_mul
    apply (circleIntegrable_log_norm_meromorphicOn hf).abs
