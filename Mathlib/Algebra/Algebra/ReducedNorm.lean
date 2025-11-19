/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
This file defines the reduced characteristic norm and trace of a central simple algebra `A` over
a field `K`.

## Main definitions
* `ReducedCharPoly e a` is the characteristic polynomial of `a : A` under the algebra isomorphism
  `e : F ⊗[K] A ≃ₐ[F] Matrix n n F`, where `F` is a splitting field of `A`.
* `ReducedNorm e a` is a map that preserves multiplication and zero that sends `a : A` to the
  determinant of `a` under the algebra isomorphism `e`.
* `ReducedTrace e a` is a `K`-linear map that sends `a : A` to the trace of `a` under the algebra
  isomorphism `e`.

## Tags
Noncommutative algebra, central simple algebra, reduced norm, reduced trace
-/

open scoped TensorProduct

variable {K F A n : Type*} [Fintype n] [DecidableEq n] [Field K] [Field F] [Algebra K F] [Ring A]
  [Algebra K A] (e : F ⊗[K] A ≃ₐ[F] Matrix n n F)

noncomputable section

/-- The reduced characteristic polynomial of an element `a` in a central simple algebra `A` over a
  field `K`, given a splitting field `F` and an algebra isomorphism
  `e : F ⊗[K] A ≃ₐ[K] Matrix n n F`. -/
def reducedCharPoly (a : A) := (e (1 ⊗ₜ a)).charpoly

/-- The reduced norm of an element `a` in a central simple algebra `A` over a field `K`, given a
  splitting field `F` and an algebra isomorphism `e`. -/
@[simps]
def reducedNorm [Nonempty n] : A →*₀ F where
  toFun a := (e (1 ⊗ₜ a)).det
  map_zero' := by simp
  map_one' := by simp [← Algebra.TensorProduct.one_def]
  map_mul' := by simp [← Matrix.det_mul, ← map_mul]

/-- The reduced trace of an element `a` in a central simple algebra `A` over a field `K`, given a
  splitting field `F` and an algebra isomorphism `e`. -/
-- @[simps]
def reducedTrace : A →ₗ[K] F :=
  Matrix.traceLinearMap n F F ∘ₗ
    LinearMap.restrictScalars K e.toLinearMap ∘ₗ {
      toFun a := 1 ⊗ₜ a
      map_add' := by simp [TensorProduct.tmul_add]
      map_smul' := by simp
    }

end

namespace ReducedCharPoly

@[simp]
theorem equalMatrixCharpoly (M : Matrix n n K) :
    reducedCharPoly (Algebra.TensorProduct.lid _ _) M = M.charpoly := by
  simp [reducedCharPoly]

end ReducedCharPoly
