/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Scalar Matrices

Given a semiring `R` and an additive commutative monoid `M` such that `M` is an `R` bimodule, we can
multiply matrices with elements in `M` on the left and right by matrices with elements in `R`.

As we do not yet have a well developed theory of bimodules in Mathlib, we make `R` commutative and
do all the scalar multiplication on the left.
-/

variable {R : Type*}  [CommSemiring R] {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

variable {m n o : Type*}

variable [Fintype n] [Fintype o]

open BigOperators

namespace ScalarMatrix

/-- `SMatrix.dotProduct v w` is the sum of the entrywise scalar products `v i • w i` -/
def dotProduct (v : n → R) (w : n → N₂) : N₂ :=
  ∑ i, v i • w i

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
   so that `r₁ • a ⬝ₛᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ₛᵥ (r₂ • b)` here. -/
@[inherit_doc]
infixl:72 " ⬝ₛᵥ " => dotProduct


lemma dotProduct_eq_Matrix_dotProduct (v : n → R) (w : n → R) : v ⬝ₛᵥ w = Matrix.dotProduct v w :=
  rfl

/-- `mulVec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mulVec M v` is the vector whose entries
    are those of `M * col v` (see `col_mulVec`). -/
def mulVec (M : Matrix m n N₂) (v : n → R) : m → N₂
  | i => v ⬝ₛᵥ (fun j => M i j)


lemma mulVec_eq_Matrix_mulVec (M : Matrix m n R) (v : n → R) : mulVec M v = Matrix.mulVec M v := by
  ext _
  rw [mulVec, Matrix.mulVec, dotProduct_eq_Matrix_dotProduct, Matrix.dotProduct_comm]

variable (R)

/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w * M * v ≠ 0`. -/
def Nondegenerate [Fintype m] (M : Matrix m m N₂) :=
  ∀ v, (∀ w, dotProduct v (mulVec (R := R) M w) = 0) → v = (0 : m → R)

variable {R}

lemma Nondegenerate_iff_Matrix_Nondegenerate {R : Type*} [CommRing R] [Fintype m]
    (M : Matrix m m R) : Nondegenerate R M ↔ Matrix.Nondegenerate M := by
  simp_rw [Nondegenerate, Matrix.Nondegenerate, mulVec_eq_Matrix_mulVec,
    dotProduct_eq_Matrix_dotProduct]

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho [Fintype m] {M : Matrix m m N₂}
    (hM : Nondegenerate R M) {v : m → R}
    (hv : ∀ w, dotProduct v (mulVec (R := R) M w) = 0) : v = 0 :=
  hM v hv

end ScalarMatrix
