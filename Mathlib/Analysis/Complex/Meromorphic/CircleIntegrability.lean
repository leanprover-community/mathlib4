/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleIntegral

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
