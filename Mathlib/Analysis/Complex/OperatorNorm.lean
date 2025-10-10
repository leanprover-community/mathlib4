/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Complex.Determinant

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

/-- The determinant of `conjLIE`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

@[simp]
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm

@[simp]
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm

@[simp]
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm

@[simp]
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap

@[simp]
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm

end Complex
