/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dual space, linear maps and matrices.

This file contains some results about matrices and dual spaces.

## Tags

matrix, linear_map, transpose, dual
-/

open Matrix Module

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type*} [CommSemiring K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

@[simp]
theorem LinearMap.toMatrix_transpose (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R := K) u) =
      (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

@[simp]
theorem Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
    Module.Dual.transpose (R := K) (Matrix.toLin B₂ B₁ M) := by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_transpose, LinearMap.toMatrix_toLin]

end Transpose

/-- The dot product as a linear equivalence to the dual. -/
@[simps] def dotProductEquiv (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n] :
    (n → R) ≃ₗ[R] Module.Dual R (n → R) where
  toFun v := ⟨⟨dotProduct v, dotProduct_add v⟩, fun t ↦ dotProduct_smul t v⟩
  map_add' v w := by ext; simp
  map_smul' t v := by ext; simp
  invFun f i := f (LinearMap.single R _ i 1)
  left_inv v := by simp
  right_inv f := by ext; simp
