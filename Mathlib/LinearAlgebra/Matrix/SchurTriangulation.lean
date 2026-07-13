/-
Copyright (c) 2025 Gordon Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gordon Hsu, Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Triangularizable

/-!
# Schur triangulation

Existence of a unitary matrix `U` and block-upper-triangular `T` with `A = U * T * star U`.

## Main results

* `Matrix.exists_unitaryGroup_blockTriangular`
* `Matrix.exists_orthonormalBasis_blockTriangular_toEuclideanLin`
-/

@[expose] public section

namespace Matrix

open Module
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜)

theorem exists_orthonormalBasis_blockTriangular_toEuclideanLin :
    ∃ b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n),
      (LinearMap.toMatrixOrthonormal b (toEuclideanLin A)).BlockTriangular id := by
  let f : Module.End 𝕜 (EuclideanSpace 𝕜 n) := toEuclideanLin A
  obtain ⟨b, hb⟩ := Module.End.exists_orthonormalBasis_blockTriangular_toMatrix_finrank f
  let e : Fin (finrank 𝕜 (EuclideanSpace 𝕜 n)) ≃o n :=
    Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm)
  let e' : Fin (finrank 𝕜 (EuclideanSpace 𝕜 n)) ≃ n := e.toEquiv
  let b' := b.reindex e'
  refine ⟨b', ?_⟩
  intro i j hji
  calc LinearMap.toMatrixOrthonormal b' f i j
      = LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j) := by
        change LinearMap.toMatrixOrthonormal (b.reindex e') f i j =
          LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j)
        rw [LinearMap.toMatrixOrthonormal_reindex b e' f]
        rfl
    _ = 0 := hb (e.symm.lt_iff_lt.mpr hji)

/-- **Schur triangulation**: unitary similarity to a block-upper-triangular matrix. -/
theorem exists_unitaryGroup_blockTriangular :
    ∃ U : Matrix.unitaryGroup n 𝕜, ∃ T : Matrix n n 𝕜,
      T.BlockTriangular id ∧ A = U * T * star (U : Matrix n n 𝕜) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_blockTriangular_toEuclideanLin A
  let c := EuclideanSpace.basisFun n 𝕜
  let U : Matrix.unitaryGroup n 𝕜 :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T : Matrix n n 𝕜 := LinearMap.toMatrixOrthonormal b (toEuclideanLin A)
  have hUT : (U : Matrix n n 𝕜) * T = A * U := by
    let cb := c.toBasis
    let bb := b.toBasis
    calc cb.toMatrix bb * LinearMap.toMatrix bb bb (toEuclideanLin A)
        = LinearMap.toMatrix cb cb (toEuclideanLin A) * cb.toMatrix bb := by simp
      _ = LinearMap.toMatrix cb cb (toLin cb cb A) * (U : Matrix n n 𝕜) := rfl
      _ = A * U := by simp
  refine ⟨U, T, hb, ?_⟩
  calc A
      = A * U * star (U : Matrix n n 𝕜) := by simp [mul_assoc]
    _ = U * T * star (U : Matrix n n 𝕜) := by rw [← hUT]

end Matrix
