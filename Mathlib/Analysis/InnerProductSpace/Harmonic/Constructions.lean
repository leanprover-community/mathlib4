/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

If `f : ℂ → F` is complex-differentiable, then `f` is harmonic. If `F = ℂ`, then so is its real
part, imaginary part, and complex conjugate. If `f` has no zero, then `log ‖f‖` is harmonic.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Complex ComplexConjugate InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {x : ℂ}

/-!
## Harmonicity of Analytic Functions on the Complex Plane
-/

set_option backward.isDefEq.respectTransparency false in
/--
Continuously complex-differentiable functions on ℂ are harmonic.
-/
theorem ContDiffAt.harmonicAt (h : ContDiffAt ℂ 2 f x) : HarmonicAt f x := by
  refine ⟨h.restrict_scalars ℝ, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := ℝ)] with a ha
  have : (iteratedFDeriv ℂ 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv ℂ 2 f a) ![1, 1]) :=
    (iteratedFDeriv ℂ 2 f a).map_smul_univ (fun _ ↦ I) ![1, 1]
  simp_all [laplacian_eq_iteratedFDeriv_complexPlane f, ← ha,
    ContinuousMultilinearMap.coe_restrictScalars]

set_option backward.isDefEq.respectTransparency false in
/-- Analytic functions on ℂ are harmonic. -/
theorem AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt ℂ f x) : HarmonicAt f x :=
  h.contDiffAt.harmonicAt

set_option backward.isDefEq.respectTransparency false in
/--
If `f : ℂ → ℂ` is complex-analytic, then its real part is harmonic.
-/
theorem AnalyticAt.harmonicAt_re {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
    HarmonicAt (fun z ↦ (f z).re) x := h.harmonicAt.comp_CLM reCLM

set_option backward.isDefEq.respectTransparency false in
/--
If `f : ℂ → ℂ` is complex-analytic, then its imaginary part is harmonic.
-/
theorem AnalyticAt.harmonicAt_im {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
    HarmonicAt (fun z ↦ (f z).im) x :=
  h.harmonicAt.comp_CLM imCLM

set_option backward.isDefEq.respectTransparency false in
/--
If `f : ℂ → ℂ` is complex-analytic, then its complex conjugate is harmonic.
-/
theorem AnalyticAt.harmonicAt_conj {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) : HarmonicAt (conj f) x :=
  (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

/-!
## Harmonicity of `log ‖analytic‖`
-/

set_option backward.isDefEq.respectTransparency false in
/- Helper lemma for AnalyticAt.harmonicAt_log_norm -/
private lemma analyticAt_harmonicAt_log_normSq {z : ℂ} {g : ℂ → ℂ} (h₁g : AnalyticAt ℂ g z)
    (h₂g : g z ≠ 0) (h₃g : g z ∈ slitPlane) :
    HarmonicAt (Real.log ∘ normSq ∘ g) z := by
  rw [harmonicAt_congr_nhds (f₂ := reCLM ∘ (conjCLE ∘ log ∘ g + log ∘ g))]
  · exact (((harmonicAt_comp_CLE_iff conjCLE).2 ((analyticAt_clog h₃g).comp h₁g).harmonicAt).add
      ((analyticAt_clog h₃g).comp h₁g).harmonicAt).comp_CLM reCLM
  · have t₀ := h₁g.differentiableAt.continuousAt.preimage_mem_nhds
      ((isOpen_slitPlane.inter isOpen_ne).mem_nhds ⟨h₃g, h₂g⟩)
    calc Real.log ∘ normSq ∘ g
    _ =ᶠ[𝓝 z] reCLM ∘ ofRealCLM ∘ Real.log ∘ normSq ∘ g := by aesop
    _ =ᶠ[𝓝 z] reCLM ∘ log ∘ ((conjCLE ∘ g) * g) := by
      filter_upwards with x
      simp only [Function.comp_apply, ofRealCLM_apply, Pi.mul_apply, conjCLE_apply]
      rw [ofReal_log, normSq_eq_conj_mul_self]
      exact normSq_nonneg (g x)
    _ =ᶠ[𝓝 z] reCLM ∘ (log ∘ conjCLE ∘ g + log ∘ g) := by
      filter_upwards [t₀] with x hx
      simp only [Function.comp_apply, Pi.mul_apply, conjCLE_apply, Pi.add_apply]
      congr
      rw [Complex.log_mul_eq_add_log_iff _ hx.2, Complex.arg_conj]
      · simp [Complex.slitPlane_arg_ne_pi hx.1, Real.pi_pos, Real.pi_nonneg]
      · simpa [ne_eq, map_eq_zero] using hx.2
    _ =ᶠ[𝓝 z] ⇑reCLM ∘ (⇑conjCLE ∘ log ∘ g + log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g ⁻¹' (Complex.slitPlane ∩ {0}ᶜ), t₀
      intro x hx
      simp only [Function.comp_apply, Pi.add_apply, conjCLE_apply]
      congr 1
      rw [← Complex.log_conj]
      simp [Complex.slitPlane_arg_ne_pi hx.1]

set_option backward.isDefEq.respectTransparency false in
/--
If `f : ℂ → ℂ` is complex-analytic without zero, then `log ‖f‖` is harmonic.
-/
theorem AnalyticAt.harmonicAt_log_norm {f : ℂ → ℂ} {z : ℂ} (h₁f : AnalyticAt ℂ f z)
    (h₂f : f z ≠ 0) :
    HarmonicAt (Real.log ‖f ·‖) z := by
  have : (Real.log ‖f ·‖) = (2 : ℝ)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Complex.norm_def, Real.log_sqrt]
    · linarith
    exact (f z).normSq_nonneg
  rw [this]
  apply HarmonicAt.const_smul
  by_cases h₃f : f z ∈ Complex.slitPlane
  · exact analyticAt_harmonicAt_log_normSq h₁f h₂f h₃f
  · rw [(by aesop : Complex.normSq ∘ f = Complex.normSq ∘ (-f))]
    exact analyticAt_harmonicAt_log_normSq h₁f.neg (by simpa)
      ((mem_slitPlane_or_neg_mem_slitPlane h₂f).resolve_left h₃f)
