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

Schur triangulation is also known as Schur decomposition or Schur triangularization. It states that
a square matrix over an algebraically closed field, for example `ℂ`, is unitarily similar to an
upper triangular matrix.

The definitions `schurTriangulationBasis`, `schurTriangulationUnitary`, and
`schurTriangulation` are noncanonical classical choices. The upper-triangular predicate is
relative to the chosen `LinearOrder` on the finite index type.

## Main definitions

- `Matrix.schurTriangulation_eq` : a square matrix over an algebraically closed field can be
  decomposed as `A = U * T * star U` where `U` is unitary and `T` is upper triangular.
- `Matrix.schurTriangulationUnitary_mul_schurTriangulation` : the corresponding intertwining
  identity `U * T = A * U`.
- `Matrix.schurTriangulationUnitary` : the chosen unitary matrix `U`.
- `Matrix.schurTriangulation` : the chosen upper triangular matrix `T`.

-/

@[expose] public section

/-! The Schur construction below specializes algebraic triangularization. The theorem
`Module.End.exists_orthonormalBasis_isUpperTriangular_toMatrix` gives an orthonormal basis in which
the associated linear map is upper triangular; this file uses that choice to construct a unitary
similarity of matrices. -/

namespace Matrix

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜)

/-- Every matrix over an algebraically closed `RCLike` field has an orthonormal basis in which its
associated linear map has an upper triangular matrix. -/
theorem exists_orthonormalBasis_isUpperTriangular_toEuclideanLin :
    ∃ b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n),
      (LinearMap.toMatrixOrthonormal b (toEuclideanLin A)).IsUpperTriangular := by
  let f : Module.End 𝕜 (EuclideanSpace 𝕜 n) := toEuclideanLin A
  let h := Module.End.exists_orthonormalBasis_isUpperTriangular_toMatrix f
  let d := h.choose
  let b := h.choose_spec.choose
  have hd : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) = d := by
    simpa using Module.finrank_eq_card_basis b.toBasis
  have hut : (LinearMap.toMatrix b.toBasis b.toBasis f).IsUpperTriangular :=
    h.choose_spec.choose_spec
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let e' : Fin d ≃ n := e.toEquiv
  let b' := b.reindex e'
  refine ⟨b', ?_⟩
  intro i j hji
  calc LinearMap.toMatrixOrthonormal b' f i j
    _ = LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j) := by
      change LinearMap.toMatrixOrthonormal (b.reindex e') f i j =
        LinearMap.toMatrixOrthonormal b f (e'.symm i) (e'.symm j)
      rw [LinearMap.toMatrixOrthonormal_reindex b e' f]
      rfl
    _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)

/-- A chosen orthonormal change of basis that induces the upper triangular form
`A.schurTriangulation` of a matrix `A` over an algebraically closed field. -/
noncomputable def schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (exists_orthonormalBasis_isUpperTriangular_toEuclideanLin A).choose

/-- The matrix of `toEuclideanLin A` in the chosen Schur basis is upper triangular. -/
theorem schurTriangulationBasis_isUpperTriangular_toEuclideanLin :
    (LinearMap.toMatrixOrthonormal (schurTriangulationBasis A)
      (toEuclideanLin A)).IsUpperTriangular :=
  (exists_orthonormalBasis_isUpperTriangular_toEuclideanLin A).choose_spec

/-- The unitary matrix that induces the upper triangular form `A.schurTriangulation` to which a
matrix `A` over an algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulationUnitary : unitaryGroup n 𝕜 where
  val := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (schurTriangulationBasis A)
  property := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ..

@[simp]
theorem coe_schurTriangulationUnitary :
    (schurTriangulationUnitary A : Matrix n n 𝕜) =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (schurTriangulationBasis A) :=
  rfl

/-- The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an
algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulation : UpperTriangular n 𝕜 where
  val := LinearMap.toMatrixOrthonormal (schurTriangulationBasis A) (toEuclideanLin A)
  property := schurTriangulationBasis_isUpperTriangular_toEuclideanLin A

@[simp]
theorem coe_schurTriangulation :
    (schurTriangulation A : Matrix n n 𝕜) =
      LinearMap.toMatrixOrthonormal (schurTriangulationBasis A) (toEuclideanLin A) :=
  rfl

/-- The chosen Schur unitary intertwines `A` with its triangular form. -/
theorem schurTriangulationUnitary_mul_schurTriangulation :
    (schurTriangulationUnitary A : Matrix n n 𝕜) *
        (schurTriangulation A : Matrix n n 𝕜) =
      A * schurTriangulationUnitary A := by
  let b := (schurTriangulationBasis A).toBasis
  let c := (EuclideanSpace.basisFun n 𝕜).toBasis
  calc c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
    _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
    _ = LinearMap.toMatrix c c (toLin c c A) * schurTriangulationUnitary A := rfl
    _ = A * schurTriangulationUnitary A := by simp

/-- **Schur triangulation**, **Schur decomposition** for matrices over an algebraically closed
field. In particular, a complex matrix can be converted to upper-triangular form by a change of
basis. In other words, any complex matrix is unitarily similar to an upper triangular matrix. -/
theorem schurTriangulation_eq :
    A = schurTriangulationUnitary A * schurTriangulation A *
        star (schurTriangulationUnitary A) := by
  let U := schurTriangulationUnitary A
  calc A
    _ = A * U * star U := by simp [mul_assoc]
    _ = U * schurTriangulation A * star U := by
      rw [← schurTriangulationUnitary_mul_schurTriangulation A]

end Matrix
