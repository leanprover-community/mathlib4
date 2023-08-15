/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Determinant

#align_import data.complex.determinant from "leanprover-community/mathlib"@"65ec59902eb17e4ab7da8d7e3d0bd9774d1b8b99"

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

/-- The determinant of `conjAe`, as a linear map. -/
@[simp]
theorem det_conjAe : LinearMap.det conjAe.toLinearMap = -1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_conjAe, Matrix.det_fin_two_of]
  simp
#align complex.det_conj_ae Complex.det_conjAe

/-- The determinant of `conjAe`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : LinearEquiv.det conjAe.toLinearEquiv = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, AlgEquiv.toLinearEquiv_toLinearMap, det_conjAe,
    Units.coe_neg_one]
#align complex.linear_equiv_det_conj_ae Complex.linearEquiv_det_conjAe

end Complex
