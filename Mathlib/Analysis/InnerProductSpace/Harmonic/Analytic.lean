/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is complex-analytic at `x`.

TODO: As soon as PR #9598 (feat(Analysis/Complex): HasPrimitives on disc) is merged, extend this to
show that `f` itself is locally the real part of a holomorphic function, and hence real-analytic.
-/

open Complex InnerProductSpace Topology

variable
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex differentiable at `x`.
-/
theorem HarmonicAt.differentiableAt_complex_partial (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) x := by
  have h₁f := hf.1
  apply differentiableAt_complex_iff_differentiableAt_real.2
  constructor
  · fun_prop
  · repeat rw [fderiv_sub]
    repeat rw [fderiv_const_smul]
    repeat rw [fderiv_comp]
    all_goals
      try fun_prop
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_smul', Pi.sub_apply,
      Function.comp_apply, ofRealCLM_apply, Pi.smul_apply, smul_eq_mul]
    repeat rw [mul_sub]
    ring_nf
    repeat rw [fderiv_clm_apply]
    all_goals
      try fun_prop
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, I_sq, neg_mul, one_mul, sub_neg_eq_add]
    rw [add_comm, sub_eq_add_neg]
    congr 1
    · rw [ofReal_inj]
      apply h₁f.isSymmSndFDerivAt (by simp)
    · have h₂f := hf.2.eq_of_nhds
      simp [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
        add_eq_zero_iff_eq_neg] at h₂f
      simp [h₂f]

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex analytic at `x`.
-/
theorem HarmonicAt.analyticAt_complex_partial (hf : HarmonicAt f x) :
    AnalyticAt ℂ (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) x :=
  DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy ↦ (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOf_harmonicAt f).mem_nhds hf)
