/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Data.Complex.Determinant

#align_import analysis.complex.operator_norm from "leanprover-community/mathlib"@"468b141b14016d54b479eb7a0fff1e360b7e3cf6"

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `Complex.reClm` (real part), `Complex.imClm` (imaginary part),
`Complex.conjCle` (conjugation), and `Complex.ofRealClm` (inclusion of `ℝ`) were introduced in
`Analysis.Complex.Basic`. This file contains a few calculations requiring more imports:
the operator norm and (for `Complex.conjCle`) the determinant.
-/


open ContinuousLinearMap

namespace Complex

/-- The determinant of `conjLie`, as a linear map. -/
@[simp]
theorem det_conjLie : LinearMap.det (conjLie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe
#align complex.det_conj_lie Complex.det_conjLie

/-- The determinant of `conjLie`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLie : LinearEquiv.det conjLie.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe
#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLie

@[simp]
theorem reClm_norm : ‖reClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reClm 1‖ := by simp
                          -- 🎉 no goals
      _ ≤ ‖reClm‖ := unit_le_op_norm _ _ (by simp)
                                             -- 🎉 no goals
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
                          -- 🎉 no goals
      _ ≤ ‖imClm‖ := unit_le_op_norm _ _ (by simp)
                                             -- 🎉 no goals
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
