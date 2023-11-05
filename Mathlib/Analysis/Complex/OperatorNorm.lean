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

/-- The determinant of `conjLie`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLie : LinearEquiv.det conjLie.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

@[simp]
theorem reClm_norm : ‖reClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reClm 1‖ := by simp
      _ ≤ ‖reClm‖ := unit_le_op_norm _ _ (by simp)

@[simp]
theorem reClm_nnnorm : ‖reClm‖₊ = 1 :=
  Subtype.ext reClm_norm

@[simp]
theorem imClm_norm : ‖imClm‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imClm I‖ := by simp
      _ ≤ ‖imClm‖ := unit_le_op_norm _ _ (by simp)

@[simp]
theorem imClm_nnnorm : ‖imClm‖₊ = 1 :=
  Subtype.ext imClm_norm

@[simp]
theorem conjCle_norm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLie.toLinearIsometry.norm_toContinuousLinearMap

@[simp]
theorem conjCle_nnorm : ‖(conjCle : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCle_norm

@[simp]
theorem ofRealClm_norm : ‖ofRealClm‖ = 1 :=
  ofRealLi.norm_toContinuousLinearMap

@[simp]
theorem ofRealClm_nnnorm : ‖ofRealClm‖₊ = 1 :=
  Subtype.ext <| ofRealClm_norm

end Complex
