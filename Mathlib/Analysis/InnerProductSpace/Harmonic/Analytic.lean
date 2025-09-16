/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is complex-analytic at `x`. If
`f` is harmonic on an open ball, then it is the real part of a function `F : ℂ → ℂ` that is
holomorphic on the ball.

TODO: Show that harmonic functions are real-analytic.
-/

open Complex InnerProductSpace Metric Topology

variable
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex differentiable at `x`.
-/
theorem HarmonicAt.differentiableAt_complex_partial (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) x := by
  have : (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) =
      (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) := by
    ext; simp
  rw [this]
  have h₁f := hf.1
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨by fun_prop, ?_⟩
  rw [fderiv_sub (by fun_prop) (by fun_prop), fderiv_const_smul (by fun_prop)]
  repeat rw [fderiv_comp]; all_goals try fun_prop
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_sub',
    ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_smul', Pi.sub_apply,
    Function.comp_apply, ofRealCLM_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
  ring_nf
  rw [fderiv_clm_apply (by fun_prop) (by fun_prop), fderiv_clm_apply (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, I_sq, neg_mul, one_mul, sub_neg_eq_add]
  rw [add_comm, sub_eq_add_neg]
  congr 1
  · norm_cast
    apply h₁f.isSymmSndFDerivAt (by simp)
  · have h₂f := hf.2.eq_of_nhds
    simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply,
      add_eq_zero_iff_eq_neg] at h₂f
    simp [h₂f]

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex analytic at `x`.
-/
theorem HarmonicAt.analyticAt_complex_partial (hf : HarmonicAt f x) :
    AnalyticAt ℂ (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) x :=
  DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy ↦ (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOf_harmonicAt f).mem_nhds hf)

/-
If a function `f : ℂ → ℝ` is harmonic on an open ball, then `f` is the real part of a function
`F : ℂ → ℂ` that is holomorphic on the ball.
-/
theorem harmonic_is_realOfHolomorphic {z : ℂ} {R : ℝ} (hf : HarmonicOnNhd f (ball z R)) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F (ball z R)) ∧ ((ball z R).EqOn (fun z ↦ (F z).re) f) := by
  by_cases hR : R ≤ 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : DifferentiableOn ℂ g (ball z R) :=
    fun x hx ↦ (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F₀, hF₀⟩ := hg.isExactOn_ball
  let F := fun x ↦ F₀ x - F₀ z + f z
  have h₁F : ∀ z₁ ∈ ball z R, HasDerivAt F (g z₁) z₁ := by
    simp_all [F]
  have h₂F : DifferentiableOn ℂ F (ball z R) :=
    fun x hx ↦ (h₁F x hx).differentiableAt.differentiableWithinAt
  have h₃F : DifferentiableOn ℝ F (ball z R) :=
    h₂F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  use F, h₂F.analyticOnNhd isOpen_ball
  rw [(by aesop : (fun z ↦ (F z).re) = Complex.reCLM ∘ F)]
  intro x hx
  apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
  · exact reCLM.differentiable.comp_differentiableOn h₃F
  · exact fun y hy ↦ (ContDiffAt.differentiableAt (hf y hy).1 one_le_two).differentiableWithinAt
  · exact isOpen_ball.uniqueDiffOn
  · intro y hy
    have h₄F := (h₁F y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy)
      (reCLM.differentiableAt.comp y h₅F), fderivWithin_eq_fderiv
      (isOpen_ball.uniqueDiffWithinAt hy) ((hf y hy).1.differentiableAt one_le_two), fderiv_comp y
      (by fun_prop) h₅F, ContinuousLinearMap.fderiv, h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
    simp [HasDerivAt.deriv (h₁F y hy), g]
  · simp_all
  · simp [F]
  · assumption
