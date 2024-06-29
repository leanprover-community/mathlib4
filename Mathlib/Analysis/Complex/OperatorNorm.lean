/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Data.Complex.Determinant

#align_import analysis.complex.operator_norm from "leanprover-community/mathlib"@"468b141b14016d54b479eb7a0fff1e360b7e3cf6"

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `Complex.reCLM` (real part), `Complex.imCLM` (imaginary part),
`Complex.conjCLE` (conjugation), and `Complex.ofRealCLM` (inclusion of `ℝ`) were introduced in
`Analysis.Complex.Basic`. This file contains a few calculations requiring more imports:
the operator norm and (for `Complex.conjCLE`) the determinant.
-/

open ContinuousLinearMap

namespace Complex

/-- The determinant of `conjLIE`, as a linear map. -/
@[simp]
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe
#align complex.det_conj_lie Complex.det_conjLIE

/-- The determinant of `conjLIE`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe
#align complex.linear_equiv_det_conj_lie Complex.linearEquiv_det_conjLIE

@[simp]
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)
#align complex.re_clm_norm Complex.reCLM_norm

@[simp]
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm
#align complex.re_clm_nnnorm Complex.reCLM_nnnorm

@[simp]
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)
#align complex.im_clm_norm Complex.imCLM_norm

@[simp]
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm
#align complex.im_clm_nnnorm Complex.imCLM_nnnorm

@[simp]
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap
#align complex.conj_cle_norm Complex.conjCLE_norm

@[simp]
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm
#align complex.conj_cle_nnorm Complex.conjCLE_nnorm

@[simp]
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap
#align complex.of_real_clm_norm Complex.ofRealCLM_norm

@[simp]
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm
#align complex.of_real_clm_nnnorm Complex.ofRealCLM_nnnorm

end Complex
