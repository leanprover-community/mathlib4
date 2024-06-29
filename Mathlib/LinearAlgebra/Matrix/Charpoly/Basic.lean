/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PolynomialAlgebra

#align_import linear_algebra.matrix.charpoly.basic from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)


/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
#align charmatrix Matrix.charmatrix

theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl
#align charmatrix_apply Matrix.charmatrix_apply

@[simp]
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

#align charmatrix_apply_eq Matrix.charmatrix_apply_eq

@[simp]
theorem charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]
#align charmatrix_apply_ne Matrix.charmatrix_apply_ne

theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub, Pi.sub_apply]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]
#align mat_poly_equiv_charmatrix Matrix.matPolyEquiv_charmatrix

theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]
#align charmatrix_reindex Matrix.charmatrix_reindex

lemma charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]

lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by
  simp only [charmatrix]
  ext (i|i) (j|j) : 2 <;> simp [diagonal]

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
#align matrix.charpoly Matrix.charpoly

theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]
#align matrix.charpoly_reindex Matrix.charpoly_reindex

lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly, charmatrix_map, ← Polynomial.coe_mapRingHom, charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]

@[simp]
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `LinearMap.aeval_self_charpoly` for the equivalent statement about endomorphisms.
-/
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [_root_.map_mul, matPolyEquiv_charmatrix] at h
  -- Because the coefficient ring `Matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [matPolyEquiv_smul_one, eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h
#align matrix.aeval_self_charpoly Matrix.aeval_self_charpoly

end Matrix
