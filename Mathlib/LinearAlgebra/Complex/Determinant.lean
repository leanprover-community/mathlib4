/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/

public section


namespace Complex

/-- The determinant of `conjAe`, as a linear map. -/
@[simp]
theorem det_conjAe : conjAe.toLinearEquiv.toLinearMap.det = -1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_conjAe, Matrix.det_fin_two_of]
  simp

/-- The determinant of `conjAe`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by simp [← Units.val_inj]

end Complex
