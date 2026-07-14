/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Orthonormal triangularization

This file connects algebraic triangularization by an invariant complete flag with the
Gram-Schmidt construction of an orthonormal basis adapted to the same flag.

## Main results

* `Module.End.exists_orthonormalBasis_isTriangularizedBy_of_isTriangularizedBy`: a triangularizing
  basis in a finite-dimensional inner product space can be replaced by an orthonormal
  triangularizing basis with the same index type.
* `Module.End.exists_orthonormalBasis_isTriangularizedBy`: an endomorphism with a triangularizing
  basis has an orthonormal triangularizing basis.
* `Module.End.exists_orthonormalBasis_isUpperTriangular_toMatrix`: in finite dimensions over an
  algebraically closed field, an endomorphism has an upper-triangular matrix in some orthonormal
  basis.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ} {f : End 𝕜 E}

/-- A triangularizing basis in a finite-dimensional inner product space can be replaced by an
orthonormal triangularizing basis with the same index type and the same complete flag. -/
theorem exists_orthonormalBasis_isTriangularizedBy_of_isTriangularizedBy
    (b : Basis (Fin n) 𝕜 E) (hb : f.IsTriangularizedBy b) :
    ∃ u : OrthonormalBasis (Fin n) 𝕜 E, f.IsTriangularizedBy u.toBasis := by
  haveI : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
  let u := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  refine ⟨u, ?_⟩
  exact Module.End.isTriangularizedBy_of_flag_eq hb fun k =>
    Module.Basis.flag_gramSchmidtOrthonormalBasis_toBasis b k

/-- If an endomorphism has a triangularizing basis in a finite-dimensional inner product space, then
it has an orthonormal triangularizing basis. -/
theorem exists_orthonormalBasis_isTriangularizedBy
    (h : ∃ n, ∃ b : Basis (Fin n) 𝕜 E, f.IsTriangularizedBy b) :
    ∃ n, ∃ u : OrthonormalBasis (Fin n) 𝕜 E, f.IsTriangularizedBy u.toBasis := by
  obtain ⟨n, b, hb⟩ := h
  obtain ⟨u, hu⟩ := exists_orthonormalBasis_isTriangularizedBy_of_isTriangularizedBy b hb
  exact ⟨n, u, hu⟩

/-- If an endomorphism has a triangularizing basis in a finite-dimensional inner product space, then
it has an upper-triangular matrix in some orthonormal basis. -/
theorem exists_orthonormalBasis_isUpperTriangular_toMatrix_of_exists_isTriangularizedBy
    (h : ∃ n, ∃ b : Basis (Fin n) 𝕜 E, f.IsTriangularizedBy b) :
    ∃ n, ∃ u : OrthonormalBasis (Fin n) 𝕜 E,
      (LinearMap.toMatrix u.toBasis u.toBasis f).IsUpperTriangular := by
  obtain ⟨n, u, hu⟩ := exists_orthonormalBasis_isTriangularizedBy h
  exact ⟨n, u, isTriangularizedBy_iff_isUpperTriangular_toMatrix.mp hu⟩

/-- In finite dimensions over an algebraically closed `RCLike` field, every endomorphism has an
upper-triangular matrix in some orthonormal basis. -/
theorem exists_orthonormalBasis_isUpperTriangular_toMatrix [IsAlgClosed 𝕜]
    [FiniteDimensional 𝕜 E] (f : End 𝕜 E) :
    ∃ n, ∃ u : OrthonormalBasis (Fin n) 𝕜 E,
      (LinearMap.toMatrix u.toBasis u.toBasis f).IsUpperTriangular :=
  exists_orthonormalBasis_isUpperTriangular_toMatrix_of_exists_isTriangularizedBy
    (Module.End.exists_isTriangularizedBy f)

end Module.End
