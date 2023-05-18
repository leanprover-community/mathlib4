/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.complex.operator_norm
! leanprover-community/mathlib commit 468b141b14016d54b479eb7a0fff1e360b7e3cf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Data.Complex.Determinant

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `complex.re_clm` (real part), `complex.im_clm` (imaginary part),
`complex.conj_cle` (conjugation), and `complex.of_real_clm` (inclusion of `ℝ`) were introduced in
`analysis.complex.operator_norm`.  This file contains a few calculations requiring more imports:
the operator norm and (for `complex.conj_cle`) the determinant.
-/


open ContinuousLinearMap

namespace Complex

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp]
theorem det_conjLie : (conjLie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
  det_conjAe
#align complex.det_conj_lie Complex.det_conjLie

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLie : conjLie.toLinearEquiv.det = -1 :=
  linearEquiv_det_conjAe
#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLie

@[simp]
theorem reClm_norm : ‖reClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reClm 1‖ := by simp
      _ ≤ ‖reClm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.re_clm_norm Complex.reClm_norm

@[simp]
theorem reClm_nnnorm : ‖reClm‖₊ = 1 :=
  Subtype.ext reClm_norm
#align complex.re_clm_nnnorm Complex.reClm_nnnorm

@[simp]
theorem imClm_norm : ‖imClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imClm I‖ := by simp
      _ ≤ ‖imClm‖ := unit_le_op_norm _ _ (by simp)
      
#align complex.im_clm_norm Complex.imClm_norm

@[simp]
theorem imClm_nnnorm : ‖imClm‖₊ = 1 :=
  Subtype.ext imClm_norm
#align complex.im_clm_nnnorm Complex.imClm_nnnorm

@[simp]
theorem conjCle_norm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLie.toLinearIsometry.norm_toContinuousLinearMap
#align complex.conj_cle_norm Complex.conjCle_norm

@[simp]
theorem conjCle_nnorm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCle_norm
#align complex.conj_cle_nnorm Complex.conjCle_nnorm

@[simp]
theorem ofRealClm_norm : ‖ofRealClm‖ = 1 :=
  ofRealLi.norm_toContinuousLinearMap
#align complex.of_real_clm_norm Complex.ofRealClm_norm

@[simp]
theorem ofRealClm_nnnorm : ‖ofRealClm‖₊ = 1 :=
  Subtype.ext <| ofRealClm_norm
#align complex.of_real_clm_nnnorm Complex.ofRealClm_nnnorm

end Complex

