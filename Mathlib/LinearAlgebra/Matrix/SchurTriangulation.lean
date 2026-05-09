/-
Copyright (c) 2025 Gordon Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gordon Hsu
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
- `LinearMap.SchurTriangulationAux.of` packages the algebraic triangularization theorem and the
  Gram-Schmidt orthonormal flag-adaptation theorem for use by the matrix API.

-/

@[expose] public section

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation`. See also
`LinearMap.SchurTriangulationAux.of` and `Matrix.schurTriangulationAux`. -/
structure SchurTriangulationAux (f : Module.End 𝕜 E) where
  /-- The dimension of the inner product space `E`. -/
  dim : ℕ
  hdim : Module.finrank 𝕜 E = dim
  /-- An orthonormal basis of `E` that induces an upper triangular form for `f`. -/
  basis : OrthonormalBasis (Fin dim) 𝕜 E
  upperTriangular : (toMatrix basis.toBasis basis.toBasis f).BlockTriangular _root_.id

end

/-! The Schur construction below specializes algebraic triangularization. First
`Module.End.exists_isTriangularizedBy` gives a basis whose complete flag is invariant; then
`Module.End.exists_orthonormalBasis_isTriangularizedBy` replaces it by an orthonormal basis adapted
to the same flag. For orthonormal bases, upper triangular entries are the same predicate as flag
invariance by `Module.End.isTriangularizedBy_iff_isUpperTriangular_toMatrix`. -/

variable [IsAlgClosed 𝕜]

/-- **Don't use this definition directly.** This is the key algorithm behind
`Matrix.schur_triangulation`. -/
noncomputable def SchurTriangulationAux.of {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : Module.End 𝕜 E) :
    SchurTriangulationAux f := by
  let h := Module.End.exists_orthonormalBasis_isTriangularizedBy
    (Module.End.exists_isTriangularizedBy f)
  let n := h.choose
  let b := h.choose_spec.choose
  have hb : f.IsTriangularizedBy b.toBasis := h.choose_spec.choose_spec
  refine
    { dim := n
      hdim := ?_
      basis := b
      upperTriangular := ?_ }
  · simpa using Module.finrank_eq_card_basis b.toBasis
  · exact Module.End.isTriangularizedBy_iff_isUpperTriangular_toMatrix.mp hb

end LinearMap

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜)

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation` for which this is their
simultaneous definition. This is `LinearMap.SchurTriangulationAux` adapted for matrices in the
Euclidean space. -/
noncomputable def schurTriangulationAux :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 := by
  let f := toEuclideanLin A
  obtain ⟨d, hd, b, hut⟩ := LinearMap.SchurTriangulationAux.of f
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
    A =
      schurTriangulationUnitary A * schurTriangulation A *
        star (schurTriangulationUnitary A) := by
  let U := schurTriangulationUnitary A
  have h : U * (schurTriangulation A).val = A * U := by
    let b := (schurTriangulationBasis A).toBasis
    let c := (EuclideanSpace.basisFun n 𝕜).toBasis
    calc c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
      _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
      _ = LinearMap.toMatrix c c (toLin c c A) * U := rfl
      _ = A * U := by simp
  calc A
    _ = A * U * star U := by simp [mul_assoc]
    _ = U * schurTriangulation A * star U := by rw [← h]

end Matrix
