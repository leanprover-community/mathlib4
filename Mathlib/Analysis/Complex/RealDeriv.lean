/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.Conformal.NormedSpace

#align_import analysis.complex.real_deriv from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-! # Real differentiability of complex-differentiable functions

`HasDerivAt.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.

`DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
differential from the complex plane into an arbitrary complex-normed space is conformal at a point
if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

`conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
function with a nonvanishing differential between the complex plane is conformal at a point if and
only if it's holomorphic or antiholomorphic at that point.

## TODO

* The classical form of Cauchy-Riemann equations
* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
throughout or antiholomorphic throughout.

## Warning

We do NOT require conformal functions to be orientation-preserving in this file.
-/


section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

open Complex

variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasStrictFDerivAt ((↑) : ℝ → ℂ) ofRealClm z := ofRealClm.hasStrictFDerivAt
  -- ⊢ HasStrictDerivAt (fun x => (e ↑x).re) e'.re z
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealClm z) :=
    h.hasStrictFDerivAt.restrictScalars ℝ
  have C : HasStrictFDerivAt re reClm (e (ofRealClm z)) := reClm.hasStrictFDerivAt
  -- ⊢ HasStrictDerivAt (fun x => (e ↑x).re) e'.re z
  -- Porting note: this should be by:
  -- simpa using (C.comp z (B.comp z A)).hasStrictDerivAt
  -- but for some reason simp can not use `ContinuousLinearMap.comp_apply`
  convert (C.comp z (B.comp z A)).hasStrictDerivAt
  -- ⊢ e'.re = ↑(ContinuousLinearMap.comp reClm (ContinuousLinearMap.comp (Continuo …
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- ⊢ e'.re = ↑reClm (↑(ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap …
  simp
  -- 🎉 no goals
#align has_strict_deriv_at.real_of_complex HasStrictDerivAt.real_of_complex

/-- If a complex function `e` is differentiable at a real point, then the function `ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equal to the real part
of the complex derivative. -/
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealClm z := ofRealClm.hasFDerivAt
  -- ⊢ HasDerivAt (fun x => (e ↑x).re) e'.re z
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealClm z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt re reClm (e (ofRealClm z)) := reClm.hasFDerivAt
  -- ⊢ HasDerivAt (fun x => (e ↑x).re) e'.re z
  -- Porting note: this should be by:
  -- simpa using (C.comp z (B.comp z A)).hasStrictDerivAt
  -- but for some reason simp can not use `ContinuousLinearMap.comp_apply`
  convert (C.comp z (B.comp z A)).hasDerivAt
  -- ⊢ e'.re = ↑(ContinuousLinearMap.comp reClm (ContinuousLinearMap.comp (Continuo …
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- ⊢ e'.re = ↑reClm (↑(ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap …
  simp
  -- 🎉 no goals
#align has_deriv_at.real_of_complex HasDerivAt.real_of_complex

theorem ContDiffAt.real_of_complex {n : ℕ∞} (h : ContDiffAt ℂ n e z) :
    ContDiffAt ℝ n (fun x : ℝ => (e x).re) z := by
  have A : ContDiffAt ℝ n ((↑) : ℝ → ℂ) z := ofRealClm.contDiff.contDiffAt
  -- ⊢ ContDiffAt ℝ n (fun x => (e ↑x).re) z
  have B : ContDiffAt ℝ n e z := h.restrict_scalars ℝ
  -- ⊢ ContDiffAt ℝ n (fun x => (e ↑x).re) z
  have C : ContDiffAt ℝ n re (e z) := reClm.contDiff.contDiffAt
  -- ⊢ ContDiffAt ℝ n (fun x => (e ↑x).re) z
  exact C.comp z (B.comp z A)
  -- 🎉 no goals
#align cont_diff_at.real_of_complex ContDiffAt.real_of_complex

theorem ContDiff.real_of_complex {n : ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex
#align cont_diff.real_of_complex ContDiff.real_of_complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reClm.smulRight f' + I • imClm.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasStrictFDerivAt.restrictScalars ℝ
#align has_strict_deriv_at.complex_to_real_fderiv' HasStrictDerivAt.complexToReal_fderiv'

theorem HasDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reClm.smulRight f' + I • imClm.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using h.hasFDerivAt.restrictScalars ℝ
  -- 🎉 no goals
#align has_deriv_at.complex_to_real_fderiv' HasDerivAt.complexToReal_fderiv'

theorem HasDerivWithinAt.complexToReal_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reClm.smulRight f' + I • imClm.smulRight f') s x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasFDerivWithinAt.restrictScalars ℝ
#align has_deriv_within_at.complex_to_real_fderiv' HasDerivWithinAt.complexToReal_fderiv'

theorem HasStrictDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasStrictFDerivAt.restrictScalars ℝ
  -- 🎉 no goals
#align has_strict_deriv_at.complex_to_real_fderiv HasStrictDerivAt.complexToReal_fderiv

theorem HasDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivAt.restrictScalars ℝ
  -- 🎉 no goals
#align has_deriv_at.complex_to_real_fderiv HasDerivAt.complexToReal_fderiv

theorem HasDerivWithinAt.complexToReal_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivWithinAt.restrictScalars ℝ
  -- 🎉 no goals
#align has_deriv_within_at.complex_to_real_fderiv HasDerivWithinAt.complexToReal_fderiv

/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z :=
  by simpa only [ofRealClm_apply, ofReal_one, mul_one] using hf.comp z ofRealClm.hasDerivAt
     -- 🎉 no goals
#align has_deriv_at.comp_of_real HasDerivAt.comp_ofReal

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealClm_apply, ofReal_one, real_smul, mul_one] using
    ofRealClm.hasDerivAt.scomp z hf
#align has_deriv_at.of_real_comp HasDerivAt.ofReal_comp

end RealDerivOfComplex

section Conformality

/-! ### Conformality of real-differentiable complex maps -/

open Complex ContinuousLinearMap

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
    This is a version of the Cauchy-Riemann equations. -/
theorem DifferentiableAt.conformalAt (h : DifferentiableAt ℂ f z) (hf' : deriv f z ≠ 0) :
    ConformalAt f z := by
  rw [conformalAt_iff_isConformalMap_fderiv, (h.hasFDerivAt.restrictScalars ℝ).fderiv]
  -- ⊢ IsConformalMap (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ f z))
  apply isConformalMap_complex_linear
  -- ⊢ fderiv ℂ f z ≠ 0
  simpa only [Ne.def, ext_ring_iff]
  -- 🎉 no goals
#align differentiable_at.conformal_at DifferentiableAt.conformalAt

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : ℂ → ℂ} {z : ℂ} :
    ConformalAt f z ↔
      (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 := by
  rw [conformalAt_iff_isConformalMap_fderiv]
  -- ⊢ IsConformalMap (fderiv ℝ f z) ↔ (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ …
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  -- ⊢ ((∃ map, restrictScalars ℝ map = fderiv ℝ f z) ∨ ∃ map, restrictScalars ℝ ma …
  apply and_congr_left
  -- ⊢ fderiv ℝ f z ≠ 0 → (((∃ map, restrictScalars ℝ map = fderiv ℝ f z) ∨ ∃ map,  …
  intro h
  -- ⊢ ((∃ map, restrictScalars ℝ map = fderiv ℝ f z) ∨ ∃ map, restrictScalars ℝ ma …
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  -- ⊢ ((∃ map, restrictScalars ℝ map = fderiv ℝ f z) ∨ ∃ map, restrictScalars ℝ ma …
  apply or_congr
  -- ⊢ (∃ map, restrictScalars ℝ map = fderiv ℝ f z) ↔ DifferentiableAt ℂ f z
  · rw [differentiableAt_iff_restrictScalars ℝ h_diff]
    -- 🎉 no goals
  rw [← conj_conj z] at h_diff
  -- ⊢ (∃ map, restrictScalars ℝ map = comp (fderiv ℝ f z) ↑conjCle) ↔ Differentiab …
  rw [differentiableAt_iff_restrictScalars ℝ (h_diff.comp _ conjCle.differentiableAt)]
  -- ⊢ (∃ map, restrictScalars ℝ map = comp (fderiv ℝ f z) ↑conjCle) ↔ ∃ g', restri …
  refine' exists_congr fun g => rfl.congr _
  -- ⊢ comp (fderiv ℝ f z) ↑conjCle = fderiv ℝ (f ∘ ↑(starRingEnd ℂ)) (↑(starRingEn …
  have : fderiv ℝ conj (conj z) = _ := conjCle.fderiv
  -- ⊢ comp (fderiv ℝ f z) ↑conjCle = fderiv ℝ (f ∘ ↑(starRingEnd ℂ)) (↑(starRingEn …
  simp [fderiv.comp _ h_diff conjCle.differentiableAt, this, conj_conj]
  -- 🎉 no goals
#align conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj

end Conformality
