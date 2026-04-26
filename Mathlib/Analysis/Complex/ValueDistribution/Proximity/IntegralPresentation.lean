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

private lemma integrable_cartanKernel_in_alpha (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    IntegrableOn (cartanKernel f R · β) (Ioc 0 (2 * π)) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
  simpa [cartanKernel, norm_sub_rev, CircleIntegrable] using circleIntegrable_log_norm_sub_const 1

private lemma integral_norm_eq_two_mul_integral_max_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Integrable g μ) (hmax : Integrable (fun x ↦ max (g x) 0) μ) :
    ∫ x, ‖g x‖ ∂μ = 2 * ∫ x, max (g x) 0 ∂μ - ∫ x, g x ∂μ := by
  have h_eq : ∀ x, ‖g x‖ = 2 * max (g x) 0 - g x := by
    intro x
    grind [norm_eq_abs]
  rw [integral_congr_ae (Eventually.of_forall h_eq), integral_sub (hmax.const_mul 2) hg,
    integral_const_mul]

/--
If `f : ℂ → ℂ` is measurable, then the Cartan kernel of integration is measurable as a function in
the two variables `α` and `β`.
-/
theorem measurable_cartanKernel (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ ↦ cartanKernel f R p.1 p.2) := by
  apply measurable_log.comp (continuous_norm.measurable.comp _)
  exact (hf.comp ((continuous_circleMap 0 R).measurable.comp measurable_snd)).sub
    ((continuous_circleMap 0 1).measurable.comp measurable_fst)

/- Formula for the `L¹` norm of an angular slice of the Cartan kernel. -/
private lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in Ioc 0 (2 * π), ‖cartanKernel f R α β‖ =
      2 * (∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  calc ∫ α, ‖cartanKernel f R α β‖ ∂μ
    _ = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - ∫ α, cartanKernel f R α β ∂μ := by
      have h_slice : Integrable (cartanKernel f R · β) μ :=
        integrable_cartanKernel_in_alpha f R β
      exact integral_norm_eq_two_mul_integral_max_sub h_slice (h_slice.sup (integrable_const 0))
    _ = 2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) - 2 * π * log⁺ ‖f (circleMap 0 R β)‖ := by
      congr
      let z := f (circleMap 0 R β)
      have h_avg : circleAverage (log ‖z - ·‖) 0 1 = log⁺ ‖z‖ := by
        simp [norm_sub_rev]
      simp only [circleAverage_def, smul_eq_mul] at h_avg
      field_simp [two_pi_pos.ne'] at h_avg
      rwa [← intervalIntegral.integral_of_le two_pi_pos.le]

/- The `L¹` norms of the angular slices of the Cartan kernel form an integrable family. -/
private lemma integrable_integral_norm_cartanKernel (h : Meromorphic f) :
    Integrable (∫ α, ‖cartanKernel f R α ·‖ ∂(volume.restrict (Ioc 0 (2 * π))))
      (volume.restrict (Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have h_meas_K : Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) :=
    measurable_cartanKernel h.measurable
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ := by
    have : CircleIntegrable (log⁺ ‖f ·‖) 0 R :=
      h.meromorphicOn.circleIntegrable_posLog_norm
    rwa [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at this
  have h_int_Bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + log 2) μ :=
    h_int_posLog.add (integrable_const _)
  have h_int_Term1 : Integrable (fun β ↦ ∫ α, max (cartanKernel f R α β) 0 ∂μ) μ := by
    apply Integrable.mono (h_int_Bound.const_mul (2 * π))
      (h_meas_K.max measurable_const).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards with β
    have h_int_nonneg : 0 ≤ ∫ α, max (cartanKernel f R α β) 0 ∂μ :=
      integral_nonneg fun _ ↦ le_max_right _ _
    have h_bound_nonneg : 0 ≤ (2 * π) * (log⁺ ‖f (circleMap 0 R β)‖ + log 2) := by
      apply mul_nonneg two_pi_pos.le
      apply add_nonneg posLog_nonneg (log_nonneg one_le_two)
    rw [norm_of_nonneg h_int_nonneg, norm_of_nonneg h_bound_nonneg]
    have : ∫ α, max (cartanKernel f R α β) 0 ∂(volume.restrict (Ioc 0 (2 * π))) ≤
        ∫ _, log⁺ ‖f (circleMap 0 R β)‖ + log 2 ∂(volume.restrict (Ioc 0 (2 * π))) := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ ↦ le_max_right _ _
      · exact integrable_const _
      · apply Eventually.of_forall
        intro α
        calc max (cartanKernel f R α β) 0
          _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
            simp [cartanKernel, posLog_def, max_comm, sub_eq_add_neg]
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
lemma integrable_cartanKernel (h : Meromorphic f) :
    Integrable (fun p ↦ cartanKernel f R p.1 p.2)
      ((volume.restrict (uIoc 0 (2 * π))).prod
       (volume.restrict (uIoc 0 (2 * π)))) := by
  simpa [uIoc_of_le two_pi_pos.le] using (integrable_prod_iff'
    (measurable_cartanKernel h.measurable).stronglyMeasurable.aestronglyMeasurable).2
    ⟨Eventually.of_forall (integrable_cartanKernel_in_alpha f R),
      integrable_integral_norm_cartanKernel h⟩

end Cartan

/--
Presentation of the proximity function as iterated circle averages.
-/
@[simp] theorem proximity_top_eq_circleAverage_circleAverage (h : Meromorphic f) :
    (fun R ↦ circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1) = proximity f ⊤ := by
  ext R
  let F : ℝ → ℝ → ℝ := Cartan.cartanKernel f R
  calc circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ α in 0..2 * π, ∫ β in 0..2 * π, F α β := by
      simp only [circleAverage, mul_comm, mul_inv_rev, smul_eq_mul, mul_assoc,
        intervalIntegral.integral_const_mul, mul_left_comm, mul_eq_mul_left_iff, inv_eq_zero,
        OfNat.ofNat_ne_zero, or_false, pi_ne_zero, F]
      aesop
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ β in 0..2 * π, ∫ α in 0..2 * π, F α β := by
      congr 1
      set μ := volume.restrict (Ioc 0 (2 * π))
      calc ∫ x in 0..2 * π, ∫ y in 0..2 * π, F x y
        _ = ∫ x, ∫ y, F x y ∂μ ∂μ := by
          simp [μ, intervalIntegral.integral_of_le two_pi_pos.le]
        _ = ∫ y, ∫ x, F x y ∂μ ∂μ := by
          apply MeasureTheory.integral_integral_swap
          simpa [uIoc_of_le two_pi_pos.le] using Cartan.integrable_cartanKernel h
        _ = ∫ y in 0..2 * π, ∫ x in 0..2 * π, F x y := by
          simp [μ, intervalIntegral.integral_of_le two_pi_pos.le]
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
  have integrable_intervalIntegral_cartanKernel_left :
      Integrable (∫ β in 0..2 * π, Cartan.cartanKernel f R · β)
        (volume.restrict (Ioc 0 (2 * π))) := by
    have h_int := Cartan.integrable_cartanKernel (R := R) h
    rw [uIoc_of_le two_pi_pos.le] at h_int
    simpa [intervalIntegral.integral_of_le two_pi_pos.le, Cartan.cartanKernel]
      using h_int.integral_prod_left
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  apply IntegrableOn.congr_fun
    (integrable_intervalIntegral_cartanKernel_left.const_mul (2 * π)⁻¹)
    (fun _ _ ↦ by simp [circleAverage, Cartan.cartanKernel]) measurableSet_Ioc

end ValueDistribution
