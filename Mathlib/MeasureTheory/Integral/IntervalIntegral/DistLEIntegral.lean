/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Displacement is at most the integral of the speed

In this file we prove several version of the following fact:
the displacement (`dist (f a) (f b)`) is at most the integral of `‖deriv f‖` over `[a, b]`.
-/
set_option backward.defeqAttrib.useBackward true


public section

open Filter Set MeasureTheory Measure Metric
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Line

variable {f : ℝ → E} {a b : ℝ}

/-- Displacement is at most the integral of an upper estimate on the speed.

Let `f : ℝ → E` be a function which is continuous on a closed interval `[a, b]`
and is differentiable on the open interval `(a, b)`.
If `B t` is an integrable upper estimate on `‖f' t‖`, `a < t < b`,
then `‖f b - f a‖ ≤ ∫ t in a..b, B t`.
-/
lemma norm_sub_le_integral_of_norm_deriv_le_of_le {B : ℝ → ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg t (ht : t ∈ Ioo a b) : deriv g t = deriv f t := by
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt <| Ioo_mem_nhds ht.1 ht.2
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Ioo a b → ‖deriv g t‖ ≤ B t :=
      hfB.mono fun t htB ht ↦ by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g, ← dist_eq_norm_sub] using this hgc hgd hgn inferInstance
  -- In a complete space, we have
  -- `‖f b - f a‖ = ‖∫ t in a..b, deriv f t‖ ≤ ∫ t in a..b, ‖deriv f t‖`
  have hfB' : (‖deriv f ·‖) ≤ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
    exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht) |>.hasDerivWithinAt
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
    exact hfB'.trans <| .of_forall fun _ ↦ le_abs_self _

/-- Let `f : ℝ → E` be a function which is continuous on `[a, b]` and is differentiable on `(a, b)`.
Suppose that `‖f' t‖ ≤ C` for a.e. `t ∈ (a, b)`.
Then the distance between `f a` and `f b`
is at most `C` times the measure of `x ∈ (a, b)` such that `f' x ≠ 0`.

This lemma is useful, if `f` is known to have zero derivative at most points of `[a, b]`. -/
lemma norm_sub_le_mul_volume_of_norm_deriv_le_of_le {C : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hnorm : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ C) :
    ‖f b - f a‖ ≤ C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
  set s := toMeasurable volume {x | deriv f x ≠ 0}
  have hsm : MeasurableSet s := by measurability
  calc
    ‖f b - f a‖ ≤ ∫ t in a..b, indicator s (fun _ ↦ C) t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd
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

end Line

section NormedSpace

open AffineMap
variable {f : E → F} {a b : E} {C r : ℝ} {s : Set E}

/-- Consider a function `f : E → F` continuous on a segment `[a, b]`
and line differentiable in the direction `b - a` at all points of the open segment `(a, b)`.

If `‖∂_{b - a} f‖ ≤ C` at a.e. all points of the open segment,
then `‖f b - f a‖ ≤ C * volume s`, where `s` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero line derivative in the direction `b - a` at `lineMap a b t`. -/
lemma norm_sub_le_mul_volume_of_norm_lineDeriv_le
    (hfc : ContinuousOn f (segment ℝ a b))
    (hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a))
    (hf' : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * volume.real {t ∈ Ioo (0 : ℝ) 1 | lineDeriv ℝ f (lineMap a b t) (b - a) ≠ 0} := by
  set g : ℝ → F := fun t ↦ f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt g (lineDeriv ℝ f (lineMap a b t) (b - a)) t := by
    have := (hfd t ht).hasLineDerivAt.scomp_of_eq (𝕜 := ℝ) t ((hasDerivAt_id t).sub_const t)
    simpa [g, lineMap_apply_module', Function.comp_def, sub_smul, add_comm _ a] using this
  suffices ‖g 1 - g 0‖ ≤ C * volume.real {t ∈ Ioo 0 1 | deriv g t ≠ 0} by
    convert this using 1
    · simp [g]
    · congr 2 with t
      simp +contextual [(hdg _ _).deriv]
  apply norm_sub_le_mul_volume_of_norm_deriv_le_of_le zero_le_one hgc
  · exact fun t ht ↦ (hdg t ht).differentiableAt.differentiableWithinAt
  · exact hf'.mono fun t ht ht_mem ↦ by simpa only [(hdg t ht_mem).deriv] using ht ht_mem

/-- Let `f : E → F` be a function differentiable on a set `s` and continuous on its closure.
Let `a`, `b` be two points such that the open segment connecting `a` to `b` is a subset of `s`.

If `‖Df‖ ≤ C` everywhere on `s` then `‖f b - f a‖ ≤ C * volume u`,
where `u` is the set of points `t ∈ Ioo 0 1`
such that `f` has nonzero derivative at `lineMap a b t`. -/
lemma norm_sub_le_mul_volume_of_norm_fderiv_le (hs : IsOpen s) (hf : DiffContOnCl ℝ f s)
    (hab : openSegment ℝ a b ⊆ s) (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * ‖b - a‖ * volume.real {t ∈ Ioo (0 : ℝ) 1 | fderiv ℝ f (lineMap a b t) ≠ 0} := by
  have hmem_s : ∀ t ∈ Ioo (0 : ℝ) 1, lineMap a b t ∈ s := fun t ht ↦
    hab <| lineMap_mem_openSegment _ a b ht
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans <| hC _ <| hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment ℝ a b) :=
    hf.continuousOn.mono <| segment_subset_closure_openSegment.trans <| closure_mono hab
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a) := fun t ht ↦
    (hf.differentiableAt hs <| hmem_s t ht).lineDifferentiableAt
  have hfC : ∀ t ∈ Ioo (0 : ℝ) 1, ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C * ‖b - a‖ := by
    intro t ht
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    · exact ContinuousLinearMap.le_of_opNorm_le _ (hC _ <| hmem_s t ht) _
    · exact hf.differentiableAt hs <| hmem_s t ht
  refine norm_sub_le_mul_volume_of_norm_lineDeriv_le hfc hfd (.of_forall hfC) |>.trans ?_
  gcongr
  · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    simp
  · simp +contextual [(hf.differentiableAt hs <| hmem_s _ ‹_›).lineDeriv_eq_fderiv]

/-- Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`,
then $f(x) - f(a) = O(‖x - a‖ ^ {r + 1})$ as `x → a`. -/
theorem sub_isBigO_norm_rpow_add_one_of_fderiv (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
    ← mul_assoc]
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
  · exact fun z hz ↦ (hε z <| hsub hz).1
  · intro z hz
    grw [(hε z <| hsub hz).2, Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

/-- Let `f : E → F` be a function differentiable in a neighborhood of `a`.
If $Df(x) = O(‖x - a‖ ^ r)$ as `x → a`, where `r ≥ 0`, and `f a = 0`,
then $f(x) = O(‖x - a‖ ^ {r + 1})$ as `x → a`. -/
theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hf₀ : f a = 0) :
    f =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

end NormedSpace
