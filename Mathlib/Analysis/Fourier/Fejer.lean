/-
Copyright (c) 2026 Nicholas Cimino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Cimino
-/

module

public import Mathlib.Analysis.Fourier.FejerKernel

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fejér's theorem on `AddCircle`

This file proves Fejér's theorem for continuous complex-valued functions on
`AddCircle T`: when `T > 0`, the Cesàro means of the symmetric Fourier partial
sums converge uniformly to the original function.

The Fejér kernel, its normalization and concentration properties, and the
convolution representation of Fejér means are developed in
`Mathlib.Analysis.Fourier.FejerKernel`.

The proof here rewrites the approximation error as an integral against
`f (x - y) - f x`, splits that integral into a neighborhood of the origin and
its complement, and controls the two pieces by uniform continuity and kernel
concentration.

The main convergence results are:

* `fejerMean_uniform_error_lt`: explicit uniform `ε`-`N` convergence;
* `tendsto_fejerMeanContinuous`: convergence in the sup-norm topology on
  continuous maps;
* `tendstoUniformly_fejerMean`: uniform convergence expressed using
  `TendstoUniformly`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]

/-!
## Error representation and local/far estimates

We rewrite the approximation error as an integral against the Fejér kernel,
then split that integral into a neighborhood of the origin and its complement.
The near part is controlled by uniform continuity, while the far part is
controlled by concentration of the kernel.
-/

/-- Each Fejér kernel is continuous on `AddCircle T`. -/
lemma continuous_fejerKernel
    {T : ℝ}
    (n : ℕ) :
    Continuous
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y) := by
  unfold fejerKernel
  fun_prop

private lemma integrable_fejerKernel_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y *
          f (x - y))
      AddCircle.haarAddCircle := by
  have htrans :
      Continuous
        (fun y : AddCircle T =>
          x - y) := by
    fun_prop
  have hftrans :
      Continuous
        (fun y : AddCircle T =>
          f (x - y)) := by
    exact f.continuous.comp htrans
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            f (x - y)) :=
    hkernel.mul hftrans
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            f (x - y))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

private lemma integrable_fejerKernel_mul_const
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y * f x)
      AddCircle.haarAddCircle := by
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have hconst :
      Continuous
        (fun _y : AddCircle T =>
          f x) := by
    fun_prop
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y * f x) :=
    hkernel.mul hconst
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y * f x)
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

/-- The error of a Fejér mean is the integral of the Fejér kernel against the
    translated difference `f (x - y) - f x`. -/
lemma fejerMean_sub_eq_integral
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x - f x =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle := by
  rw [fejerMean_eq_integral_fejerKernel]
  have hnorm :
      (∫ y : AddCircle T,
          fejerKernel (T := T) n y
            ∂AddCircle.haarAddCircle) = 1 :=
    integral_fejerKernel (T := T) n
  calc
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) - f x
        =
      (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) -
      (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f x
          ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_mul_const]
      rw [hnorm]
      simp
    _ =
      ∫ y : AddCircle T,
        (fejerKernel (T := T) n y * f (x - y) -
          fejerKernel (T := T) n y * f x)
          ∂AddCircle.haarAddCircle := by
      rw [← MeasureTheory.integral_sub]
      · exact
          integrable_fejerKernel_mul_translate
            (T := T) f n x
      · exact
          integrable_fejerKernel_mul_const
            (T := T) f n x
    _ =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring

private lemma exists_neighborhood_uniform_diff_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ U : Set (AddCircle T),
      IsOpen U ∧
      (0 : AddCircle T) ∈ U ∧
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    f.uniform_continuity ε hε
  refine ⟨Metric.ball 0 δ, Metric.isOpen_ball, ?_, ?_⟩
  · simp [hδpos]
  · intro x y hy
    have hyδ :
        dist y 0 < δ := by
      simpa [Metric.mem_ball] using hy
    have hdist :
        dist (x - y) x < δ := by
      simpa [dist_eq_norm, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hyδ
    have hf :
        dist (f (x - y)) (f x) < ε :=
      hδ hdist
    simpa [Complex.dist_eq] using hf

/-- The Fejér kernels converge uniformly to zero outside any open neighborhood of the origin. -/
lemma fejerKernel_tendsto_zero_uniformly_outside_neighborhood
    {T : ℝ} [Fact (0 < T)]
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n →
          ∀ x : AddCircle T, x ∉ U →
            (fejerKernel (T := T) n x).re < ε := by
  have hK :
      IsCompact (Uᶜ : Set (AddCircle T)) :=
    hU.isClosed_compl.isCompact
  have h0K :
      (0 : AddCircle T) ∉ Uᶜ := by
    simpa using h0
  intro ε hε
  obtain ⟨N, hN⟩ :=
    fejerKernel_tendsto_zero_uniformly_on_compact
      (T := T) Uᶜ hK h0K ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply hN n hn x
  simpa using hx

private lemma norm_sub_translate_le_two_norm
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (x y : AddCircle T) :
    ‖f (x - y) - f x‖ ≤ 2 * ‖f‖ := by
  calc
    ‖f (x - y) - f x‖
        ≤ ‖f (x - y)‖ + ‖f x‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le (f (x - y)) (-f x)
    _ ≤ ‖f‖ + ‖f‖ := by
      gcongr
      · exact ContinuousMap.norm_coe_le_norm f (x - y)
      · exact ContinuousMap.norm_coe_le_norm f x
    _ = 2 * ‖f‖ := by
      ring

private lemma norm_fejerKernel_mul_diff_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    2 * ‖f‖ * (fejerKernel (T := T) n y).re := by
  rw [norm_mul]
  have hkernel_nonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have hkernel_eq_real :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hkernel_norm :
      ‖fejerKernel (T := T) n y‖ =
        (fejerKernel (T := T) n y).re := by
    rw [hkernel_eq_real]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hkernel_nonneg
  rw [hkernel_norm]
  have hdiff :=
    norm_sub_translate_le_two_norm
      (T := T) f x y
  nlinarith

private lemma norm_fejerKernel_mul_diff_le_of_diff_le
    {T : ℝ}
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T)
    (ε : ℝ)
    (hdiff : ‖f (x - y) - f x‖ ≤ ε) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    ε * (fejerKernel (T := T) n y).re := by
  rw [norm_mul]
  have hkernel_nonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have hkernel_eq_real :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hkernel_norm :
      ‖fejerKernel (T := T) n y‖ =
        (fejerKernel (T := T) n y).re := by
    rw [hkernel_eq_real]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hkernel_nonneg
  rw [hkernel_norm]
  have hmul :=
    mul_le_mul_of_nonneg_left hdiff hkernel_nonneg
  simpa [mul_comm] using hmul

private lemma norm_fejerKernel_mul_diff_le_on_neighborhood
    {T : ℝ}
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (ε : ℝ)
    (hU :
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε)
    (y : AddCircle T)
    (hy : y ∈ U) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    ε * (fejerKernel (T := T) n y).re := by
  apply norm_fejerKernel_mul_diff_le_of_diff_le
    (T := T) f n x y ε
  exact le_of_lt (hU x y hy)

private lemma integrable_fejerKernel_mul_diff
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y *
          (f (x - y) - f x))
      AddCircle.haarAddCircle := by
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have htrans :
      Continuous
        (fun y : AddCircle T =>
          x - y) := by
    fun_prop
  have hftrans :
      Continuous
        (fun y : AddCircle T =>
          f (x - y)) := by
    exact f.continuous.comp htrans
  have hdiff :
      Continuous
        (fun y : AddCircle T =>
          f (x - y) - f x) := by
    exact hftrans.sub continuous_const
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            (f (x - y) - f x)) :=
    hkernel.mul hdiff
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            (f (x - y) - f x))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

private lemma fejerMean_sub_eq_integral_add_compl
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (hU : IsOpen U) :
    fejerMean (T := T) f n x - f x =
      (∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle) +
      (∫ y : AddCircle T in Uᶜ,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle) := by
  rw [fejerMean_sub_eq_integral]
  symm
  exact
    MeasureTheory.integral_add_compl
      hU.measurableSet
      (integrable_fejerKernel_mul_diff
        (T := T) f n x)

/-- Each Fejér kernel is integrable with respect to normalized Haar measure. -/
lemma integrable_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y)
      AddCircle.haarAddCircle := by
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y)
        AddCircle.haarAddCircle :=
    (continuous_fejerKernel (T := T) n).locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

/-- The normalized Haar integral of the real part of the Fejér kernel is one. -/
lemma integral_fejerKernel_re
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ y : AddCircle T,
        (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle) = 1 := by
  have h :=
    integral_re
      (integrable_fejerKernel (T := T) n)
  rw [integral_fejerKernel (T := T) n] at h
  simpa using h

/-- Since the Fejér kernel is real and nonnegative, its norm equals its real part. -/
lemma norm_fejerKernel_eq_re
    {T : ℝ}
    (n : ℕ)
    (y : AddCircle T) :
    ‖fejerKernel (T := T) n y‖ =
      (fejerKernel (T := T) n y).re := by
  have hnonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have heq :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  rw [heq]
  rw [Complex.norm_real]
  exact Real.norm_of_nonneg hnonneg

/-- The normalized Haar integral of the norm of the Fejér kernel is one. -/
lemma integral_norm_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y‖
          ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [norm_fejerKernel_eq_re (T := T) n]
  exact integral_fejerKernel_re (T := T) n

private lemma norm_integral_fejerKernel_mul_diff_on_neighborhood_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (hUmeas : MeasurableSet U)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hU :
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε) :
    ‖∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
      ≤ ε := by
  let μU :=
    AddCircle.haarAddCircle.restrict U
  have hnorm_int :
      ‖∫ y : AddCircle T,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂μU‖
        ≤
      ∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
        ∂μU := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hleft_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖)
        μU := by
    exact
      (integrable_fejerKernel_mul_diff
        (T := T) f n x).norm.restrict
  have hre_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          (fejerKernel (T := T) n y).re)
        AddCircle.haarAddCircle := by
    exact
      (integrable_fejerKernel (T := T) n).re
  have hright_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ε * (fejerKernel (T := T) n y).re)
        μU := by
    exact
      (hre_int.const_mul ε).restrict
  have hpoint :
      ∀ᵐ y : AddCircle T ∂μU,
        ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ≤
        ε * (fejerKernel (T := T) n y).re := by
    apply MeasureTheory.ae_restrict_of_forall_mem hUmeas
    intro y hy
    exact
      norm_fejerKernel_mul_diff_le_on_neighborhood
        (T := T) f n x U ε hU y hy
  have hmono :
      (∫ y : AddCircle T,
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ∂μU)
        ≤
      ∫ y : AddCircle T,
        ε * (fejerKernel (T := T) n y).re
        ∂μU := by
    exact
      MeasureTheory.integral_mono_ae
        hleft_int
        hright_int
        hpoint
  have hrestrict :
      (∫ y : AddCircle T in U,
          (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle)
        ≤ 1 := by
    have hμ :
        AddCircle.haarAddCircle.restrict U
          ≤ AddCircle.haarAddCircle := by
      exact MeasureTheory.Measure.restrict_le_self
    have hnonneg :
        0 ≤ᵐ[AddCircle.haarAddCircle]
          fun y : AddCircle T =>
            (fejerKernel (T := T) n y).re := by
      filter_upwards with y
      exact fejerKernel_nonneg (T := T) n y
    have hmeasure :=
      MeasureTheory.integral_mono_measure
        hμ
        hnonneg
        hre_int
    rw [integral_fejerKernel_re (T := T) n] at hmeasure
    exact hmeasure
  calc
    ‖∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
        ≤
      ∫ y : AddCircle T in U,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
          ∂AddCircle.haarAddCircle := hnorm_int
    _ ≤
      ∫ y : AddCircle T in U,
        ε * (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle := hmono
    _ =
      ε *
        (∫ y : AddCircle T in U,
          (fejerKernel (T := T) n y).re
            ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ ε * 1 := by
      exact mul_le_mul_of_nonneg_left hrestrict hε
    _ = ε := by
      ring

private lemma norm_fejerKernel_mul_diff_le_of_re_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T)
    (δ : ℝ)
    (hkernel :
      (fejerKernel (T := T) n y).re ≤ δ) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    2 * ‖f‖ * δ := by
  have h :=
    norm_fejerKernel_mul_diff_le
      (T := T) f n x y
  have hcoef :
      0 ≤ 2 * ‖f‖ := by
    positivity
  exact
    le_trans h
      (mul_le_mul_of_nonneg_left hkernel hcoef)

private lemma norm_fejerKernel_mul_diff_le_outside_neighborhood
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U)
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ∀ y : AddCircle T, y ∉ U →
            ‖fejerKernel (T := T) n y *
                (f (x - y) - f x)‖
              ≤
            2 * ‖f‖ * δ := by
  obtain ⟨N, hN⟩ :=
    fejerKernel_tendsto_zero_uniformly_outside_neighborhood
      (T := T) U hU h0 δ hδ
  refine ⟨N, ?_⟩
  intro n hn x y hy
  apply norm_fejerKernel_mul_diff_le_of_re_le
    (T := T) f n x y δ
  exact le_of_lt (hN n hn y hy)

private lemma norm_integral_fejerKernel_mul_diff_outside_neighborhood_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U)
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ‖∫ y : AddCircle T in Uᶜ,
              fejerKernel (T := T) n y *
                (f (x - y) - f x)
                ∂AddCircle.haarAddCircle‖
            ≤
          2 * ‖f‖ * δ := by
  obtain ⟨N, hN⟩ :=
    norm_fejerKernel_mul_diff_le_outside_neighborhood
      (T := T) f U hU h0 δ hδ
  refine ⟨N, ?_⟩
  intro n hn x
  let μC :=
    AddCircle.haarAddCircle.restrict Uᶜ
  let C : ℝ :=
    2 * ‖f‖ * δ
  have hCnonneg :
      0 ≤ C := by
    dsimp [C]
    positivity
  have hnorm_int :
      ‖∫ y : AddCircle T,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂μC‖
        ≤
      ∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
        ∂μC := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hleft_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖)
        μC := by
    exact
      (integrable_fejerKernel_mul_diff
        (T := T) f n x).norm.restrict
  have hconst_int :
      MeasureTheory.Integrable
        (fun _y : AddCircle T => C)
        AddCircle.haarAddCircle := by
    exact integrable_const C
  have hright_int :
      MeasureTheory.Integrable
        (fun _y : AddCircle T => C)
        μC := by
    exact hconst_int.restrict
  have hpoint :
      ∀ᵐ y : AddCircle T ∂μC,
        ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ≤ C := by
    apply MeasureTheory.ae_restrict_of_forall_mem
      hU.measurableSet.compl
    intro y hy
    have hyU : y ∉ U := by
      simpa using hy
    dsimp [C]
    exact hN n hn x y hyU
  have hmono :
      (∫ y : AddCircle T,
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ∂μC)
        ≤
      ∫ _y : AddCircle T,
        C
        ∂μC := by
    exact
      MeasureTheory.integral_mono_ae
        hleft_int
        hright_int
        hpoint
  have hrestrict :
      (∫ _y : AddCircle T in Uᶜ,
          C
          ∂AddCircle.haarAddCircle)
        ≤ C := by
    have hμ :
        AddCircle.haarAddCircle.restrict Uᶜ
          ≤ AddCircle.haarAddCircle := by
      exact MeasureTheory.Measure.restrict_le_self
    have hnonneg :
        ∀ᵐ _y : AddCircle T ∂AddCircle.haarAddCircle,
          0 ≤ C := by
      exact Filter.Eventually.of_forall (fun _ => hCnonneg)
    have hmeasure :=
      MeasureTheory.integral_mono_measure
        hμ
        hnonneg
        hconst_int
    have hfull :
        (∫ _y : AddCircle T,
            C
            ∂AddCircle.haarAddCircle) = C := by
      simp
    rw [hfull] at hmeasure
    exact hmeasure
  calc
    ‖∫ y : AddCircle T in Uᶜ,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
        ≤
      ∫ y : AddCircle T in Uᶜ,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
          ∂AddCircle.haarAddCircle := hnorm_int
    _ ≤
      ∫ _y : AddCircle T in Uᶜ,
        C
        ∂AddCircle.haarAddCircle := hmono
    _ ≤ C := hrestrict
    _ = 2 * ‖f‖ * δ := by
      rfl

/-!
## Fejér's theorem

The following results establish uniform convergence of the Fejér means of a
continuous complex-valued function on `AddCircle T`.

We first prove an explicit uniform ε-N estimate, then package this result as
convergence in the sup norm on continuous maps and as `TendstoUniformly`.
-/

/-- Fejér's theorem in explicit uniform `ε`-`N` form: the Fejér means of a
    continuous function converge uniformly to the function. -/
lemma fejerMean_uniform_error_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ‖fejerMean (T := T) f n x - f x‖ < ε := by
  have hε4 :
      0 < ε / 4 := by
    positivity
  obtain ⟨U, hUopen, h0U, hUdiff⟩ :=
    exists_neighborhood_uniform_diff_lt
      (T := T) f (ε / 4) hε4
  let δ : ℝ :=
    ε / (8 * (‖f‖ + 1))
  have hnorm_nonneg :
      0 ≤ ‖f‖ := norm_nonneg f
  have hnorm_one_pos :
      0 < ‖f‖ + 1 := by
    linarith
  have hδ :
      0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N, hNfar⟩ :=
    norm_integral_fejerKernel_mul_diff_outside_neighborhood_le
      (T := T) f U hUopen h0U δ hδ
  refine ⟨N, ?_⟩
  intro n hn x
  have hnear :
      ‖∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖
        ≤ ε / 4 := by
    exact
      norm_integral_fejerKernel_mul_diff_on_neighborhood_le
        (T := T)
        f n x U hUopen.measurableSet
        (ε / 4)
        (le_of_lt hε4)
        hUdiff
  have hfar :
      ‖∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖
        ≤ 2 * ‖f‖ * δ := by
    exact hNfar n hn x
  have hfar_small :
      2 * ‖f‖ * δ ≤ ε / 4 := by
    dsimp [δ]
    have hratio :
        ‖f‖ / (‖f‖ + 1) ≤ 1 := by
      apply (div_le_one hnorm_one_pos).2
      linarith
    calc
      2 * ‖f‖ * (ε / (8 * (‖f‖ + 1))) =
          (ε / 4) * (‖f‖ / (‖f‖ + 1)) := by
        field_simp [ne_of_gt hnorm_one_pos]
        ring
      _ ≤ (ε / 4) * 1 := by
        exact
          mul_le_mul_of_nonneg_left
            hratio
            (le_of_lt hε4)
      _ = ε / 4 := by
        ring
  have hsplit :=
    fejerMean_sub_eq_integral_add_compl
      (T := T) f n x U hUopen
  rw [hsplit]
  calc
    ‖(∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle) +
      (∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle)‖
        ≤
      ‖∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖ +
      ‖∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖ := by
      exact norm_add_le _ _
    _ ≤ ε / 4 + ε / 4 := by
      exact add_le_add hnear (le_trans hfar hfar_small)
    _ < ε := by
      linarith

/-- The `n`th Fejér mean of a continuous function is continuous. -/
lemma continuous_fejerMean
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ) :
    Continuous
      (fun x : AddCircle T =>
        fejerMean (T := T) f n x) := by
  rw [show
    (fun x : AddCircle T =>
      fejerMean (T := T) f n x) =
    (fun x : AddCircle T =>
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x)) by
    funext x
    exact fejerMean_eq_weighted_fourier_sum
      (T := T) f n x]
  fun_prop

/-- The `n`th Fejér mean bundled as a continuous map `AddCircle T → ℂ`. -/
noncomputable def fejerMeanContinuous
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ) :
    C(AddCircle T, ℂ) :=
  ⟨fun x =>
      fejerMean (T := T) f n x,
    continuous_fejerMean (T := T) f n⟩

/-- Evaluating the bundled continuous Fejér mean agrees with `fejerMean`. -/
@[simp]
lemma fejerMeanContinuous_apply
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMeanContinuous (T := T) f n x =
      fejerMean (T := T) f n x := by
  rfl

/-- The bundled Fejér means eventually lie within any positive sup-norm distance of `f`. -/
lemma norm_fejerMeanContinuous_sub_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ‖fejerMeanContinuous (T := T) f n - f‖ < ε := by
  obtain ⟨N, hN⟩ :=
    fejerMean_uniform_error_lt
      (T := T) f ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  intro x
  simpa using hN n hn x

/-- The bundled Fejér means converge to `f` in the sup-norm topology on continuous maps. -/
theorem tendsto_fejerMeanContinuous
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    Filter.Tendsto
      (fun n : ℕ =>
        fejerMeanContinuous (T := T) f n)
      Filter.atTop
      (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    norm_fejerMeanContinuous_sub_lt
      (T := T) f ε hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa [dist_eq_norm] using hN n hn

/-- The Fejér means of a continuous complex-valued function on `AddCircle T`
    converge uniformly to the function. -/
theorem tendstoUniformly_fejerMean
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    TendstoUniformly
      (fun n : ℕ =>
        fun x : AddCircle T =>
          fejerMean (T := T) f n x)
      f
      Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    fejerMean_uniform_error_lt
      (T := T) f ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro x
  calc
    dist (f x) (fejerMean (T := T) f n x) =
        dist (fejerMean (T := T) f n x) (f x) := by
      exact dist_comm _ _
    _ =
        ‖fejerMean (T := T) f n x - f x‖ := by
      rw [Complex.dist_eq]
    _ < ε := hN n hn x

end AddCircle
