/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.Matrix.Order

/-!
# Schur Product Theorem

The **Schur product theorem** states that the Hadamard (entrywise) product of two
positive semidefinite Hermitian matrices is positive semidefinite (and positive
definite if both inputs are). The proof uses
`Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker` to reduce to the Kronecker product.

## Main declarations

* `Matrix.PosSemidef.hadamard`: the Hadamard product of positive semidefinite matrices is
  positive semidefinite.
* `Matrix.PosDef.hadamard`: the Hadamard product of positive definite matrices is
  positive definite.

## References

* [I. Schur, *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen
  Veränderlichen*][schur1911]
-/

@[expose] public section

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- **Schur product theorem** (positive semidefinite version): the Hadamard (entrywise) product
of positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support → ι)
    have hBs := hB.submatrix ((↑) : x.support → ι)
    rw [submatrix_hadamard, posSemidef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_nonneg _
  simp_rw [RCLike.star_def, hadamard_apply, Finsupp.sum,
    ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  exact hAB.2 (x.subtypeDomain (· ∈ x.support))

/-- **Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite. -/
theorem PosDef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hB.submatrix Subtype.coe_injective
    rw [submatrix_hadamard, posDef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y hy ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    refine (PosDef.kronecker hAs hBs).dotProduct_mulVec_pos ?_
    rwa [ne_eq, vec_eq_zero_iff, diagonal_eq_zero]
  simp_rw [RCLike.star_def, hadamard_apply, Finsupp.sum,
    ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  refine hAB.2 ?_
  simp_rw [← Finsupp.support_nonempty_iff, Finsupp.support_subtypeDomain,
    Finset.subtype_mem_eq_attach, Finset.attach_nonempty_iff]
  exact Finsupp.support_nonempty_iff.mpr hx

end Matrix
