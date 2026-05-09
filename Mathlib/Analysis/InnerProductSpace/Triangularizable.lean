/-
Copyright (c) 2026 Maria Grazia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maria Grazia
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Orthonormal triangularization

This file connects algebraic triangularization by an invariant complete flag with the
Gram-Schmidt construction of an orthonormal basis adapted to the same flag.

## Main results

* `Module.End.orthonormalBasis_isTriangularizedBy`: a triangularizing basis in a finite-dimensional
  inner product space can be replaced by an orthonormal triangularizing basis with the same index
  type.
* `Module.End.exists_orthonormalBasis_isTriangularizedBy`: the corresponding existential form.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ} {f : End 𝕜 E}

/-- A triangularizing basis in a finite-dimensional inner product space can be replaced by an
orthonormal triangularizing basis with the same index type and the same complete flag. -/
theorem orthonormalBasis_isTriangularizedBy (b : Basis (Fin n) 𝕜 E)
    (hb : f.IsTriangularizedBy b) :
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
  obtain ⟨u, hu⟩ := orthonormalBasis_isTriangularizedBy b hb
  exact ⟨n, u, hu⟩

end Module.End
