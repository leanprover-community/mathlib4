/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

#align_import linear_algebra.matrix.mv_polynomial from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an mv_polynomial ring.
In particular, we provide `Matrix.mvPolynomialX` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/

set_option linter.uppercaseLean3 false

variable {m n R S : Type*}

namespace Matrix

variable (m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
noncomputable def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)
#align matrix.mv_polynomial_X Matrix.mvPolynomialX

-- TODO: set as an equation lemma for `mv_polynomial_X`, see mathlib4#3024
@[simp]
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl
#align matrix.mv_polynomial_X_apply Matrix.mvPolynomialX_apply

variable {m n R}

/-- Any matrix `A` can be expressed as the evaluation of `Matrix.mvPolynomialX`.

This is of particular use when `MvPolynomial (m × n) R` is an integral domain but `S` is
not, as if the `MvPolynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)
#align matrix.mv_polynomial_X_map_eval₂ Matrix.mvPolynomialX_map_eval₂

/-- A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `RingHom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_eval Matrix.mvPolynomialX_mapMatrix_eval

variable (R)

/-- A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `AlgHom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_aeval Matrix.mvPolynomialX_mapMatrix_aeval

variable (m)

/-- In a nontrivial ring, `Matrix.mvPolynomialX m m R` has non-zero determinant. -/
theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, RingHom.map_zero] at this
  exact zero_ne_one this
#align matrix.det_mv_polynomial_X_ne_zero Matrix.det_mvPolynomialX_ne_zero

end Matrix
