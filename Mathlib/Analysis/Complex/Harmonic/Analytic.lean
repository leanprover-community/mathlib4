/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is complex-analytic at `x`. If
`f` is harmonic on an open ball, then it is the real part of a function `F : ℂ → ℂ` that is
holomorphic on the ball.  This implies in particular that harmonic functions are real-analytic.
-/

public section

open Complex InnerProductSpace Metric Set Topology

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

set_option backward.isDefEq.respectTransparency false in
/-
If a function `f : ℂ → ℝ` is harmonic on an open ball, then `f` is the real part of a function
`F : ℂ → ℂ` that is holomorphic on the ball.
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : ℂ} {R : ℝ}
    (hf : HarmonicOnNhd f (ball z R)) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F (ball z R)) ∧ ((ball z R).EqOn (fun z ↦ (F z).re) f) := by
  by_cases hR : R ≤ 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : DifferentiableOn ℂ g (ball z R) :=
    fun x hx ↦ (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F, hF⟩ := hg.isExactOn_ball.with_val_at z (f z)
  have h₁F : DifferentiableOn ℂ F (ball z R) :=
    fun x hx ↦ (hF.2 x hx).differentiableAt.differentiableWithinAt
  have h₂F : DifferentiableOn ℝ F (ball z R) := h₁F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  use F, h₁F.analyticOnNhd isOpen_ball
  rw [(by aesop : (fun z ↦ (F z).re) = Complex.reCLM ∘ F)]
  intro x hx
  apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
  · exact reCLM.differentiable.comp_differentiableOn h₂F
  · exact fun y hy ↦ (ContDiffAt.differentiableAt (hf y hy).1 two_ne_zero).differentiableWithinAt
  · exact isOpen_ball.uniqueDiffOn
  · intro y hy
    have h₄F := (hF.2 y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy)
      (reCLM.differentiableAt.comp y h₅F), fderivWithin_eq_fderiv
      (isOpen_ball.uniqueDiffWithinAt hy) ((hf y hy).1.differentiableAt two_ne_zero), fderiv_comp y
      (by fun_prop) h₅F, ContinuousLinearMap.fderiv, h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [map_add, map_smul, map_smul]
    simp [HasDerivAt.deriv (hF.2 y hy), g]
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias harmonic_is_realOfHolomorphic :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq

set_option backward.isDefEq.respectTransparency false in
/--
If a function `f : ℂ → ℝ` is harmonic, then `f` is the real part of a holomorphic function.
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f univ) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F univ) ∧ ((fun z ↦ (F z).re) = f) := by
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : Differentiable ℂ g :=
    fun x ↦ (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F, hF⟩ := hg.isExactOn_univ.with_val_at 0 (f 0)
  have h₁F : ∀ z₁, HasDerivAt F (g z₁) z₁ := by simp_all
  have h₂F : Differentiable ℂ F := fun x ↦ (h₁F x).differentiableAt
  have h₃F : Differentiable ℝ F := h₂F.restrictScalars (𝕜 := ℝ)
  use F, (h₂F.differentiableOn).analyticOnNhd isOpen_univ
  ext x
  rw [← Complex.reCLM_apply, ← Function.comp_apply (f := reCLM)]
  refine (convex_univ).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := 0) (by fun_prop) ?hd ?_ ?heq ?_ ?_ ?_
  case hd => exact hf.contDiffOn.differentiableOn two_ne_zero
  case heq =>
    intro y hy
    simp only [fderivWithin_univ]
    rw [fderiv_comp y (by fun_prop) (by fun_prop)]
    ext x
    trans fderiv ℝ f y (x.re • (1 : ℂ) + x.im • (I : ℂ))
    · simp only [map_smul, map_add]
      simp [(h₁F y).hasFDerivAt.restrictScalars ℝ |>.fderiv, g]
    · simp
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias InnerProductSpace.harmonic_is_realOfHolomorphic_univ :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq

set_option backward.isDefEq.respectTransparency false in
/-
Harmonic functions are real analytic.
TODO: Prove this for harmonic functions on an arbitrary f.d. inner product space (not just on `ℂ`).
-/
theorem HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt ℝ f x := by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOf_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun _ hy ↦ h₂ε hy)
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy ↦ h₂F.symm hy))]
  exact (reCLM.analyticAt (F x)).comp (h₁F x (mem_ball_self h₁ε)).restrictScalars
