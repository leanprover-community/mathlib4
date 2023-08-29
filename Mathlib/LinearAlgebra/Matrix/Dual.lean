/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import linear_algebra.matrix.dual from "leanprover-community/mathlib"@"738c19f572805cff525a93aa4ffbdf232df05aa8"

/-!
# Dual space, linear maps and matrices.

This file contains some results on the matrix corresponding to the
transpose of a linear map (in the dual space).

## Tags

matrix, linear_map, transpose, dual
-/


open Matrix

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

@[simp]
theorem LinearMap.toMatrix_transpose (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R := K) u) =
      (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  -- ⊢ ↑(toMatrix (Basis.dualBasis B₂) (Basis.dualBasis B₁)) (↑Module.Dual.transpos …
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]
#align linear_map.to_matrix_transpose LinearMap.toMatrix_transpose

@[simp]
theorem Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
    Module.Dual.transpose (R := K) (Matrix.toLin B₂ B₁ M) := by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  -- ⊢ ↑(LinearMap.toMatrix (Basis.dualBasis B₁) (Basis.dualBasis B₂)) (↑(toLin (Ba …
  rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_transpose, LinearMap.toMatrix_toLin]
  -- 🎉 no goals
#align matrix.to_lin_transpose Matrix.toLin_transpose

end Transpose
