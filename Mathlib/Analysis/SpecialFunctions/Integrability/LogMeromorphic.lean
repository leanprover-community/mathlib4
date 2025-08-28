/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Integrability for Logarithms of Meromorphic Functions

We establish integrability for functions of the form `log ‖meromorphic‖`. In the real setting, these
functions are interval integrable over every interval of the real line. This implies in particular
that logarithms of trigonometric functions are interval integrable. In the complex setting, the
functions are circle integrable over every circle in the complex plane.
-/

open Filter Interval MeasureTheory MeromorphicOn Metric Real

/-!
## Interval Integrability for Logarithms of Real Meromorphic Functions
-/

section IntervalIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
theorem intervalIntegrable_log_norm_meromorphicOn (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], meromorphicOrderAt f u ≠ ⊤
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
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto

/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
theorem intervalIntegrable_posLog_norm_meromorphicOn (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply (intervalIntegrable_log_norm_meromorphicOn hf).const_mul
  · apply (intervalIntegrable_log_norm_meromorphicOn hf).abs.const_mul

/--
If `f` is real-meromorphic on a compact interval, then `log ∘ f` is interval integrable on this
interval.
-/
theorem _root_.MeromorphicOn.intervalIntegrable_log {f : ℝ → ℝ} (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ∘ f) volume a b := by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact intervalIntegrable_log_norm_meromorphicOn hf

/--
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ sin` is interval
integrable over every interval.
-/
theorem intervalIntegrable_log_sin : IntervalIntegrable (log ∘ sin) volume a b :=
  analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log

/--
Special case of `MeromorphicOn.intervalIntegrable_log`: The function `log ∘ cos` is interval
integrable over every interval.
-/
theorem intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume a b :=
  analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log

end IntervalIntegrable

/-!
## Circle Integrability for Logarithms of Complex Meromorphic Functions
-/

section CircleIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {c : ℂ} {R : ℝ} {f : ℂ → E}

/--
If `f` is complex meromorphic on a circle in the complex plane, then `log ‖f ·‖` is circle
integrable over that circle.
-/
theorem circleIntegrable_log_norm_meromorphicOn (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log ‖f ·‖) c R := by
  by_cases t₀ : ∀ u : (sphere c |R|), meromorphicOrderAt f u ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      apply intervalIntegrable_log_norm_meromorphicOn
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
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_sphere (by simp) c
      (abs_nonneg R))] at t₀
    push_neg at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

/--
Variant of `circleIntegrable_log_norm_meromorphicOn` for non-negative radii.
-/
theorem circleIntegrable_log_norm_meromorphicOn_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 ≤ R) :
    CircleIntegrable (log ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact circleIntegrable_log_norm_meromorphicOn hf

/--
Variant of `circleIntegrable_log_norm_meromorphicOn` for factorized rational functions.
-/
theorem circleIntegrable_log_norm_factorizedRational {R : ℝ} {c : ℂ} (D : ℂ → ℤ) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R :=
  CircleIntegrable.finsum (fun _ ↦ (circleIntegrable_log_norm_meromorphicOn
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn).const_smul)

/--
If `f` is complex meromorphic on a circle in the complex plane, then `log⁺ ‖f ·‖` is circle
integrable over that circle.
-/
theorem circleIntegrable_posLog_norm_meromorphicOn (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply (circleIntegrable_log_norm_meromorphicOn hf).const_mul
  · apply (circleIntegrable_log_norm_meromorphicOn hf).abs.const_mul

/--
Variant of `circleIntegrable_posLog_norm_meromorphicOn` for non-negative radii.
-/
theorem circleIntegrable_posLog_norm_meromorphicOn_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 ≤ R) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact circleIntegrable_posLog_norm_meromorphicOn hf

end CircleIntegrable
