/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.PosDef

#align_import linear_algebra.matrix.ldl from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-! # LDL decomposition

This file proves the LDL-decomposition of matrices: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

 * `LDL.lower` is the lower triangular matrix `L`.
 * `LDL.lowerInv` is the inverse of the lower triangular matrix `L`.
 * `LDL.diag` is the diagonal matrix `D`.

## Main result

* `LDL.lower_conj_diag` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lowerInv_triangular`.

-/


variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [LinearOrder n] [IsWellOrder n (· < ·)] [LocallyFiniteOrderBot n]

section set_options

set_option linter.uppercaseLean3 false
set_option quotPrecheck false
local notation "⟪" x ", " y "⟫ₑ" =>
  @inner 𝕜 _ _ ((WithLp.equiv 2 _).symm x) ((WithLp.equiv _ _).symm y)

open Matrix

open scoped Matrix ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `Pi.basisFun`. -/
noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n → 𝕜) _ (_ : _) (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
    (Pi.basisFun 𝕜 n)
#align LDL.lower_inv LDL.lowerInv

theorem LDL.lowerInv_eq_gramSchmidtBasis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (_ : _) (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
            (Pi.basisFun 𝕜 n)))ᵀ := by
  letI := NormedAddCommGroup.ofMatrix hS.transpose
  letI := InnerProductSpace.ofMatrix hS.transpose
  ext i j
  rw [LDL.lowerInv, Basis.coePiBasisFun.toMatrix_eq_transpose, coe_gramSchmidtBasis]
  rfl
#align LDL.lower_inv_eq_gram_schmidt_basis LDL.lowerInv_eq_gramSchmidtBasis

noncomputable instance LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS) := by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (_ : _) (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
        (Pi.basisFun 𝕜 n))
  infer_instance
#align LDL.invertible_lower_inv LDL.invertibleLowerInv

theorem LDL.lowerInv_orthogonal {i j : n} (h₀ : i ≠ j) :
    ⟪LDL.lowerInv hS i, Sᵀ *ᵥ LDL.lowerInv hS j⟫ₑ = 0 :=
  @gramSchmidt_orthogonal 𝕜 _ _ (_ : _) (InnerProductSpace.ofMatrix hS.transpose) _ _ _ _ _ _ _ h₀
#align LDL.lower_inv_orthogonal LDL.lowerInv_orthogonal

/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diagEntries : n → 𝕜 := fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ
#align LDL.diag_entries LDL.diagEntries

/-- The diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)
#align LDL.diag LDL.diag

theorem LDL.lowerInv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [←
    @gramSchmidt_triangular 𝕜 (n → 𝕜) _ (_ : _) (InnerProductSpace.ofMatrix hS.transpose) n _ _ _
      i j hij (Pi.basisFun 𝕜 n),
    Pi.basisFun_repr, LDL.lowerInv]
#align LDL.lower_inv_triangular LDL.lowerInv_triangular

/-- Inverse statement of **LDL decomposition**: we can conjugate a positive definite matrix
by some lower triangular matrix and get a diagonal matrix. -/
theorem LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ := by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_piLp_equiv_symm, star_star, hij,
    diagonal_apply_eq, Matrix.mul_assoc]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose, transpose_map, transpose_transpose, dotProduct_mulVec,
      (LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm, ← inner_conj_symm,
      mulVec_transpose, EuclideanSpace.inner_piLp_equiv_symm, ← RCLike.star_def, ←
      star_dotProduct_star, dotProduct_comm, star_star]
    rfl
#align LDL.diag_eq_lower_inv_conj LDL.diag_eq_lowerInv_conj

/-- The lower triangular matrix `L` of the LDL decomposition. -/
noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹
#align LDL.lower LDL.lower

/-- **LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.  -/
theorem LDL.lower_conj_diag : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S := by
  rw [LDL.lower, conjTranspose_nonsing_inv, Matrix.mul_assoc,
    Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS),
    Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS
#align LDL.lower_conj_diag LDL.lower_conj_diag

end set_options
