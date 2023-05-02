/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module data.complex.determinant
! leanprover-community/mathlib commit 65ec59902eb17e4ab7da8d7e3d0bd9774d1b8b99
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

/-- The determinant of `conj_ae`, as a linear map. -/
@[simp]
theorem det_conjAe : conjAe.toLinearMap.det = -1 :=
  by
  rw [← LinearMap.det_toMatrix basis_one_I, to_matrix_conj_ae, Matrix.det_fin_two_of]
  simp
#align complex.det_conj_ae Complex.det_conjAe

/-- The determinant of `conj_ae`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, ← LinearEquiv.toLinearMap_eq_coe,
    AlgEquiv.toLinearEquiv_toLinearMap, det_conj_ae, Units.coe_neg_one]
#align complex.linear_equiv_det_conj_ae Complex.linearEquiv_det_conjAe

end Complex

