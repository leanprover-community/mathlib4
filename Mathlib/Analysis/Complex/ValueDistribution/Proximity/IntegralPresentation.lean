/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Integral Presentation of the Proximity Function

If `f : ℂ → ℂ` is meromorphic, this file establishes a presentation of the proximity function
`proximity f ⊤` as iterated circle averages. This statement can be used to compare the proximity-
and logarithmic counting functions, and is one of the key ingredients in the proof of Cartan's
classic formula for the characteristic function.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter MeasureTheory Real Set

namespace ValueDistribution

variable {f : ℂ → ℂ} {R : ℝ}

namespace Cartan

/-!
### Integrability of the Cartan Kernel

The proof of the integral presentation of the proximity function relies on an extended computation,
applying Fubini's theorem to the Cartan kernel of integration. This section defines the kernel and
establishes its integrability, as a function of two variables.
-/

/--
Given `f : ℂ → ℂ` and `R : ℝ`, define the Cartan kernel of integration as the function
`α β ↦ log ‖f (circleMap 0 R β) - circleMap 0 1 α‖`.
-/
noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

/--
For every function `f : ℂ → ℂ`, the Cartan kernel of integration `cartanKernel f R α β` is
integrable as a function in `α`.
-/
lemma integrableOn_cartanKernel_left (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    IntegrableOn (cartanKernel f R · β) (Ioc 0 (2 * π)) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
  simpa [cartanKernel, norm_sub_rev, CircleIntegrable] using circleIntegrable_log_norm_sub_const 1

/--
If `f : ℂ → ℂ` is measurable, then the Cartan kernel of integration is measurable as a function in
the two variables `α` and `β`.
-/
@[fun_prop]
theorem measurable_cartanKernel (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ ↦ cartanKernel f R p.1 p.2) := by
  unfold cartanKernel; fun_prop

/- Formula for the `L¹` norm of an angular slice of the Cartan kernel. -/
private lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in Ioc 0 (2 * π), ‖cartanKernel f R α β‖ =
      2 * (∫ α, (cartanKernel f R α β)⁺ ∂(volume.restrict (Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  calc ∫ α, ‖cartanKernel f R α β‖ ∂μ
    _ = 2 * (∫ α, (cartanKernel f R α β)⁺ ∂μ) - ∫ α, cartanKernel f R α β ∂μ :=
      integral_abs_eq_two_mul_integral_posPart_sub_integral (integrableOn_cartanKernel_left f R β)
    _ = 2 * (∫ α, (cartanKernel f R α β)⁺ ∂μ) - 2 * π * log⁺ ‖f (circleMap 0 R β)‖ := by
      congr
      set z := f (circleMap 0 R β)
      suffices h_avg : circleAverage (log ‖z - ·‖) 0 1 = log⁺ ‖z‖ by
        convert congr(2 * π * $h_avg)
        simp [circleAverage_def, field, cartanKernel, intervalIntegral.integral_of_le two_pi_pos.le]
      simp [norm_sub_rev]

/-
If `f : ℂ → ℂ` is meromorphic,, then the `L¹` norms of the angular slices of the Cartan kernel form
an integrable family.
-/
lemma integrable_integral_norm_cartanKernel (h : Meromorphic f) :
    Integrable (∫ α, ‖cartanKernel f R α ·‖ ∂(volume.restrict (Ioc 0 (2 * π))))
      (volume.restrict (Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have h_meas_K : Measurable (fun a : ℝ × ℝ ↦ (cartanKernel f R a.1 a.2)⁺) := by fun_prop
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ := by
    have : CircleIntegrable (log⁺ ‖f ·‖) 0 R := h.meromorphicOn.circleIntegrable_posLog_norm
    rwa [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at this
  have h_int_Bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + log 2) μ :=
    h_int_posLog.add (integrable_const _)
  have h_int_Term1 : Integrable (fun β ↦ ∫ α, (cartanKernel f R α β)⁺ ∂μ) μ := by
    apply Integrable.mono (h_int_Bound.const_mul (2 * π))
      h_meas_K.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards with β
    have h_int_nonneg : 0 ≤ ∫ α, (cartanKernel f R α β)⁺ ∂μ := by positivity
    have h_bound_nonneg : 0 ≤ (2 * π) * (log⁺ ‖f (circleMap 0 R β)‖ + log 2) := by
      positivity [posLog_nonneg (x := ‖f (circleMap 0 R β)‖)]
    rw [norm_of_nonneg h_int_nonneg, norm_of_nonneg h_bound_nonneg]
    have : ∫ α, (cartanKernel f R α β)⁺ ∂(volume.restrict (Ioc 0 (2 * π))) ≤
        ∫ _, log⁺ ‖f (circleMap 0 R β)‖ + log 2 ∂(volume.restrict (Ioc 0 (2 * π))) := by
      refine integral_mono_of_nonneg (.of_forall (by simp [posPart])) (integrable_const _)
        (.of_forall ?_)
      intro α
      calc (cartanKernel f R α β)⁺
        _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
          simp [cartanKernel, posLog_def, posPart, max_comm, sub_eq_add_neg]
        _ ≤ log⁺ ‖f (circleMap 0 R β)‖ + log⁺ ‖-circleMap 0 1 α‖ + log 2 :=
          posLog_norm_add_le (f (circleMap 0 R β)) (-circleMap 0 1 α)
        _ = log⁺ ‖f (circleMap 0 R β)‖ + log 2 := by
          simp [norm_circleMap_zero, add_comm]
    rwa [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ,
      mul_comm, volume_real_Ioc_of_le two_pi_pos.le, sub_zero] at this
  exact Integrable.congr ((h_int_Term1.const_mul 2).sub (h_int_posLog.const_mul (2 * π)))
    (Eventually.of_forall fun β ↦ (integral_norm_cartanKernel_eq f R β).symm)

/--
If `f : ℂ → ℂ` is meromorphic, then the Cartan kernel of integration is integrable as a function in
the two variables `α` and `β`.
-/
theorem integrableOn_cartanKernel (h : Meromorphic f) :
    IntegrableOn (fun p ↦ cartanKernel f R p.1 p.2) (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := h.measurable
  simpa [uIoc_of_le two_pi_pos.le] using (integrable_prod_iff' (by fun_prop)).2
    ⟨Eventually.of_forall (integrableOn_cartanKernel_left f R),
      integrable_integral_norm_cartanKernel h⟩

/--
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then the function
`β ↦ ∫ α in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
lemma integrableOn_intervalIntegral_cartanKernel_left (h : Meromorphic f) :
    IntegrableOn (∫ α in 0..2 * π, Cartan.cartanKernel f R α ·) (Ioc 0 (2 * π)) := by
  have h_int := Cartan.integrableOn_cartanKernel (R := R) h
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at h_int
  simpa [IntegrableOn, intervalIntegral.integral_of_le two_pi_pos.le, Cartan.cartanKernel]
    using h_int.integral_prod_right

/--
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then the function
`α ↦ ∫ β in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
lemma integrableOn_intervalIntegral_cartanKernel_right (h : Meromorphic f) :
    IntegrableOn (∫ β in 0..2 * π, Cartan.cartanKernel f R · β) (Ioc 0 (2 * π)) := by
  have h_int := Cartan.integrableOn_cartanKernel (R := R) h
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at h_int
  simpa [IntegrableOn, intervalIntegral.integral_of_le two_pi_pos.le, Cartan.cartanKernel]
    using h_int.integral_prod_left

end Cartan

/--
Presentation of the proximity function as iterated circle averages.
-/
theorem circleAverage_circleAverage_eq_proximity_top (h : Meromorphic f) :
    (fun R ↦ circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1) = proximity f ⊤ := by
  ext R
  let F : ℝ → ℝ → ℝ := Cartan.cartanKernel f R
  calc circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ α in 0..2 * π, ∫ β in 0..2 * π, F α β := by
      simp [circleAverage, F, Cartan.cartanKernel, mul_assoc]
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ β in 0..2 * π, ∫ α in 0..2 * π, F α β := by
      rw [MeasureTheory.intervalIntegral_intervalIntegral_swap]
      exact Cartan.integrableOn_cartanKernel h
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, ((2 * π)⁻¹ * ∫ α in 0..2 * π, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, log⁺ ‖f (circleMap 0 R β)‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro β hβ
      calc (2 * π)⁻¹ * ∫ α in 0..2 * π, F α β
        _ = circleAverage (log ‖f (circleMap 0 R β) - ·‖) 0 1 := by
          simp [F, circleAverage, Cartan.cartanKernel]
        _ = log⁺ ‖f (circleMap 0 R β)‖ := by
          simp [norm_sub_rev]
    _ = circleAverage (log⁺ ‖f ·‖) 0 R := by
      simp [circleAverage, intervalIntegral.integral_of_le two_pi_pos.le]

/--
Complementary statement to `proximity_top_eq_circleAverage_circleAverage`, providing circle
integrability of the integrand.
-/
theorem circleIntegrable_circleAverage_log_norm_sub (h : Meromorphic f) :
    CircleIntegrable (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, circleAverage_zero, norm_sub_rev, circleIntegrable_log_norm_sub_const]
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  apply IntegrableOn.congr_fun
    ((Cartan.integrableOn_intervalIntegral_cartanKernel_right (R := R) h).const_mul (2 * π)⁻¹)
    (fun _ _ ↦ by simp [circleAverage, Cartan.cartanKernel]) measurableSet_Ioc

end ValueDistribution
