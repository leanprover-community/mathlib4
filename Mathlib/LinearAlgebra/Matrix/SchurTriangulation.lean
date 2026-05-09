/-
Copyright (c) 2025 Gordon Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gordon Hsu, Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Block
/-! # Schur triangulation

Schur triangulation is more commonly known as Schur decomposition or Schur triangularization, but
"triangulation" makes the API more readable. It states that a square matrix over an algebraically
closed field, e.g., `ℂ`, is unitarily similar to an upper triangular matrix.

## Main definitions

- `Matrix.schur_triangulation` : a matrix `A : Matrix n n 𝕜` with `𝕜` being algebraically closed can
  be decomposed as `A = U * T * star U` where `U` is unitary and `T` is upper triangular.
- `Matrix.schurTriangulationUnitary` : the unitary matrix `U` as previously stated.
- `Matrix.schurTriangulation` : the upper triangular matrix `T` as previously stated.

-/

@[expose] public section

/-! The Schur construction below specializes algebraic triangularization. First
`Module.End.exists_isTriangularizedBy` gives a basis whose complete flag is invariant; then
`Module.End.exists_orthonormalBasis_isTriangularizedBy` replaces it by an orthonormal basis adapted
to the same flag. For orthonormal bases, upper triangular entries are the same predicate as flag
invariance by `Module.End.isTriangularizedBy_iff_isUpperTriangular_toMatrix`. -/

namespace Matrix

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜)

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation` for which this is their
simultaneous definition. -/
noncomputable def schurTriangulationAux :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 := by
  let f : Module.End 𝕜 (EuclideanSpace 𝕜 n) := toEuclideanLin A
  let h := Module.End.exists_orthonormalBasis_isTriangularizedBy
    (Module.End.exists_isTriangularizedBy f)
  let d := Classical.choose h
  let hb_exists := Classical.choose_spec h
  let b := Classical.choose hb_exists
  have hb : f.IsTriangularizedBy b.toBasis := Classical.choose_spec hb_exists
  have hd : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) = d := by
    simpa using Module.finrank_eq_card_basis b.toBasis
  have hut : (LinearMap.toMatrix b.toBasis b.toBasis f).IsUpperTriangular :=
    Module.End.isTriangularizedBy_iff_isUpperTriangular_toMatrix.mp hb
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let e' : Fin d ≃ n := e.toEquiv
  let b' := b.reindex e'
  let B := LinearMap.toMatrixOrthonormal b' f
  refine ⟨b', B, ?_⟩
  intro i j hji
  calc LinearMap.toMatrixOrthonormal b' f i j
    _ = LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j) := by
      change LinearMap.toMatrixOrthonormal (b.reindex e') f i j =
        LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j)
      rw [LinearMap.toMatrixOrthonormal_reindex b e' f]
      rfl
    _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)

/-- The change of basis that induces the upper triangular form `A.schurTriangulation` of a matrix
`A` over an algebraically closed field. -/
noncomputable def schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (schurTriangulationAux A).1

/-- The unitary matrix that induces the upper triangular form `A.schurTriangulation` to which a
matrix `A` over an algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulationUnitary : unitaryGroup n 𝕜 where
  val := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (schurTriangulationBasis A)
  property := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ..

/-- The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an
algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulation : UpperTriangular n 𝕜 :=
  (schurTriangulationAux A).2

/-- **Schur triangulation**, **Schur decomposition** for matrices over an algebraically closed
field. In particular, a complex matrix can be converted to upper-triangular form by a change of
basis. In other words, any complex matrix is unitarily similar to an upper triangular matrix. -/
lemma schur_triangulation :
    A = schurTriangulationUnitary A * schurTriangulation A *
        star (schurTriangulationUnitary A) := by
  let U := schurTriangulationUnitary A
  have h : U * (schurTriangulation A).val = A * U := by
    let b := (schurTriangulationBasis A).toBasis
    let c := (EuclideanSpace.basisFun n 𝕜).toBasis
    calc c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
      _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
      _ = LinearMap.toMatrix c c (toLin c c A) * U := rfl
      _ = A * U := by simp
  have hstar : (star U : Matrix n n 𝕜) = star (U : Matrix n n 𝕜) := rfl
  calc A
    _ = A * 1 := by rw [mul_one]
    _ = A * ((U : Matrix n n 𝕜) * (star U : Matrix n n 𝕜)) := by
      rw [Matrix.mem_unitaryGroup_iff.mp U.property]
    _ = A * U * star U := by
      change A * ((U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜)) =
        A * (U : Matrix n n 𝕜) * (star U : Matrix n n 𝕜)
      rw [← hstar, mul_assoc]
    _ = U * schurTriangulation A * star U := by rw [← h]

end Matrix
