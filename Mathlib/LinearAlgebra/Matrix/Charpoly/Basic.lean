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

-- porting note: these imports are no longer needed
--import Mathlib.Tactic.ApplyFun
--import Mathlib.Tactic.Squeeze

noncomputable section

universe u v w

open Polynomial Matrix BigOperators Polynomial

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

open Finset

/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
#align charmatrix charmatrix

theorem charmatrix_apply (M : Matrix n n R) (i j : n) :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl
#align charmatrix_apply charmatrix_apply

@[simp]
theorem charmatrix_apply_eq (M : Matrix n n R) (i : n) :
    charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

#align charmatrix_apply_eq charmatrix_apply_eq

@[simp]
theorem charmatrix_apply_ne (M : Matrix n n R) (i j : n) (h : i ≠ j) :
    charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]
#align charmatrix_apply_ne charmatrix_apply_ne

theorem matPolyEquiv_charmatrix (M : Matrix n n R) : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub, Pi.sub_apply]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]
#align mat_poly_equiv_charmatrix matPolyEquiv_charmatrix

theorem charmatrix_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m) (M : Matrix n n R) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]
#align charmatrix_reindex charmatrix_reindex

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def Matrix.charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
#align matrix.charpoly Matrix.charpoly

theorem Matrix.charpoly_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]
#align matrix.charpoly_reindex Matrix.charpoly_reindex

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `LinearMap.aeval_self_charpoly` for the equivalent statement about endomorphisms.
-/
theorem Matrix.aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [matPolyEquiv.map_mul, matPolyEquiv_charmatrix] at h
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
