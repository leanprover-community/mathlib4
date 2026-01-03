/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Displacement is at most the integral of the speed

In this file we prove several version of the following fact:
the displacement (`dist (f a) (f b)`) is at most the integral of `‖deriv f‖` over `[a, b]`.
-/


@[expose] public section

open Filter Set MeasureTheory Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dist_le_integral_of_norm_deriv_le_of_le {f : ℝ → E} {B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) : dist (f a) (f b) ≤ ∫ t in a..b, B t := by
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg : ∀ t ∈ Ioo a b, deriv g t = deriv f t := by
      intro t ht
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt <| Ioo_mem_nhds ht.1 ht.2
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Ioo a b → ‖deriv g t‖ ≤ B t :=
      hfB.mono fun t htB ht ↦ by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g] using this hgc hgd hgn inferInstance
  have hfB' : (‖deriv f ·‖) ≤ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [dist_eq_norm_sub', ← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
    exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht) |>.hasDerivWithinAt
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
    exact hfB'.trans <| .of_forall fun _ ↦ le_abs_self _

lemma dist_le_mul_volume_of_norm_deriv_le_of_le {f : ℝ → E} {a b C : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hnorm : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ C) :
    dist (f a) (f b) ≤ C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
  set s := toMeasurable volume {x | deriv f x ≠ 0}
  have hsm : MeasurableSet s := by measurability
  calc
    dist (f a) (f b) ≤ ∫ t in a..b, indicator s (fun _ ↦ C) t := by
      apply dist_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem ↦ ?_
        apply le_indicator_apply
        · exact fun ht' ↦ ht ht_mem
        · simp only [s, norm_le_zero_iff]
          exact not_imp_comm.2 fun h ↦ subset_toMeasurable _ _ h
      · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
        refine (integrableOn_const ?_ ?_).indicator hsm <;> simp
    _ = C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
      rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
        integral_indicator hsm, Measure.restrict_restrict hsm,
        setIntegral_const, smul_eq_mul, mul_comm]
      simp only [s, Measure.real,
        Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Ioo]
      simp only [inter_def, mem_setOf_eq, and_comm]
