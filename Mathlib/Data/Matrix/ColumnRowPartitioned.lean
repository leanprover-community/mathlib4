/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-! # Block Matrices from Rows and Columns

This file provides the basic definitions of matrices composed from columns and rows.
The concatenation of two matrices with the same row indices can be expressed as
`A = fromCols A₁ A₂` the concatenation of two matrices with the same column indices
can be expressed as `B = fromRows B₁ B₂`.

We then provide a few lemmas that deal with the products of these with each other and
with block matrices

## Tags
column matrices, row matrices, column row block matrices
-/

namespace Matrix

variable {R : Type*}
variable {m m₁ m₂ n n₁ n₂ : Type*}

/-- Concatenate together two matrices A₁[m₁ × N] and A₂[m₂ × N] with the same columns (N) to get a
bigger matrix indexed by [(m₁ ⊕ m₂) × N] -/
def fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) : Matrix (m₁ ⊕ m₂) n R :=
  of (Sum.elim A₁ A₂)

/-- Concatenate together two matrices B₁[m × n₁] and B₂[m × n₂] with the same rows (M) to get a
bigger matrix indexed by [m × (n₁ ⊕ n₂)] -/
def fromCols (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) : Matrix m (n₁ ⊕ n₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

/-- Given a column partitioned matrix extract the first column -/
def toCols₁ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₁ R := of fun i j => (A i (Sum.inl j))

/-- Given a column partitioned matrix extract the second column -/
def toCols₂ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₂ R := of fun i j => (A i (Sum.inr j))

/-- Given a row partitioned matrix extract the first row -/
def toRows₁ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₁ n R := of fun i j => (A (Sum.inl i) j)

/-- Given a row partitioned matrix extract the second row -/
def toRows₂ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₂ n R := of fun i j => (A (Sum.inr i) j)

@[deprecated (since := "2024-12-11")] alias fromColumns := fromCols
@[deprecated (since := "2024-12-11")] alias toColumns₁ := toCols₁
@[deprecated (since := "2024-12-11")] alias toColumns₂ := toCols₂

@[simp]
lemma fromRows_apply_inl (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₁) (j : n) :
    (fromRows A₁ A₂) (Sum.inl i) j = A₁ i j := rfl

@[simp]
lemma fromRows_apply_inr (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₂) (j : n) :
    (fromRows A₁ A₂) (Sum.inr i) j = A₂ i j := rfl

@[simp]
lemma fromCols_apply_inl (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₁) :
    (fromCols A₁ A₂) i (Sum.inl j) = A₁ i j := rfl

@[deprecated (since := "2024-12-11")] alias fromColumns_apply_inl := fromCols_apply_inl

@[simp]
lemma fromCols_apply_inr (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₂) :
    (fromCols A₁ A₂) i (Sum.inr j) = A₂ i j := rfl

@[deprecated (since := "2024-12-11")] alias fromColumns_apply_inr := fromCols_apply_inr

@[simp]
lemma toRows₁_apply (A : Matrix (m₁ ⊕ m₂) n R) (i : m₁) (j : n) :
    (toRows₁ A) i j = A (Sum.inl i) j := rfl

@[simp]
lemma toRows₂_apply (A : Matrix (m₁ ⊕ m₂) n R) (i : m₂) (j : n) :
    (toRows₂ A) i j = A (Sum.inr i) j := rfl

@[simp]
lemma toRows₁_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₁ (fromRows A₁ A₂) = A₁ := rfl

@[simp]
lemma toRows₂_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₂ (fromRows A₁ A₂) = A₂ := rfl

@[simp]
lemma toCols₁_apply (A : Matrix m (n₁ ⊕ n₂) R) (i : m) (j : n₁) :
    (toCols₁ A) i j = A i (Sum.inl j) := rfl

@[deprecated (since := "2024-12-11")] alias toColumns₁_apply := toCols₁_apply

@[simp]
lemma toCols₂_apply (A : Matrix m (n₁ ⊕ n₂) R) (i : m) (j : n₂) :
    (toCols₂ A) i j = A i (Sum.inr j) := rfl

@[deprecated (since := "2024-12-11")] alias toColumns₂_apply := toCols₂_apply

@[simp]
lemma toCols₁_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toCols₁ (fromCols A₁ A₂) = A₁ := rfl

@[deprecated (since := "2024-12-11")] alias toColumns₁_fromColumns := toCols₁_fromCols

@[simp]
lemma toCols₂_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toCols₂ (fromCols A₁ A₂) = A₂ := rfl

@[deprecated (since := "2024-12-11")] alias toColumns₂_fromColumns := toCols₂_fromCols

@[simp]
lemma fromCols_toCols (A : Matrix m (n₁ ⊕ n₂) R) :
    fromCols A.toCols₁ A.toCols₂ = A := by
  ext i (j | j) <;> simp

@[deprecated (since := "2024-12-11")] alias fromColumns_toColumns := fromCols_toCols

@[simp]
lemma fromRows_toRows (A : Matrix (m₁ ⊕ m₂) n R) : fromRows A.toRows₁ A.toRows₂ = A := by
  ext (i | i) j <;> simp

lemma fromRows_inj : Function.Injective2 (@fromRows R m₁ m₂ n) := by
  intros x1 x2 y1 y2
  simp [← Matrix.ext_iff]

lemma fromCols_inj : Function.Injective2 (@fromCols R m n₁ n₂) := by
  intros x1 x2 y1 y2
  simp only [funext_iff, ← Matrix.ext_iff]
  aesop

@[deprecated (since := "2024-12-11")] alias fromColumns_inj := fromCols_inj

lemma fromCols_ext_iff (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (B₁ : Matrix m n₁ R)
    (B₂ : Matrix m n₂ R) :
    fromCols A₁ A₂ = fromCols B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromCols_inj.eq_iff

@[deprecated (since := "2024-12-11")] alias fromColumns_ext_iff := fromCols_ext_iff

lemma fromRows_ext_iff (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B₁ : Matrix m₁ n R)
    (B₂ : Matrix m₂ n R) :
    fromRows A₁ A₂ = fromRows B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromRows_inj.eq_iff

/-- A column partitioned matrix when transposed gives a row partitioned matrix with columns of the
initial matrix transposed to become rows. -/
lemma transpose_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    transpose (fromCols A₁ A₂) = fromRows (transpose A₁) (transpose A₂) := by
  ext (i | i) j <;> simp

@[deprecated (since := "2024-12-11")] alias transpose_fromColumns := transpose_fromCols

/-- A row partitioned matrix when transposed gives a column partitioned matrix with rows of the
initial matrix transposed to become columns. -/
lemma transpose_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    transpose (fromRows A₁ A₂) = fromCols (transpose A₁) (transpose A₂) := by
  ext i (j | j) <;> simp

section Neg

variable [Neg R]

/-- Negating a matrix partitioned by rows is equivalent to negating each of the rows. -/
@[simp]
lemma fromRows_neg (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    -fromRows A₁ A₂ = fromRows (-A₁) (-A₂) := by
  ext (i | i) j <;> simp

/-- Negating a matrix partitioned by columns is equivalent to negating each of the columns. -/
@[simp]
lemma fromCols_neg (A₁ : Matrix n m₁ R) (A₂ : Matrix n m₂ R) :
    -fromCols A₁ A₂ = fromCols (-A₁) (-A₂) := by
  ext i (j | j) <;> simp

@[deprecated (since := "2024-12-11")] alias fromColumns_neg := fromCols_neg

end Neg

@[simp]
lemma fromCols_fromRows_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromCols (fromRows B₁₁ B₂₁) (fromRows B₁₂ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

@[deprecated (since := "2024-12-11")]
alias fromColumns_fromRows_eq_fromBlocks := fromCols_fromRows_eq_fromBlocks

@[simp]
lemma fromRows_fromCols_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromRows (fromCols B₁₁ B₁₂) (fromCols B₂₁ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

@[deprecated (since := "2024-12-11")]
alias fromRows_fromColumn_eq_fromBlocks := fromRows_fromCols_eq_fromBlocks

section Semiring

variable [Semiring R]

@[simp]
lemma fromRows_mulVec [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (v : n → R) :
    fromRows A₁ A₂ *ᵥ v = Sum.elim (A₁ *ᵥ v) (A₂ *ᵥ v) := by
  ext (_ | _) <;> rfl

@[simp]
lemma vecMul_fromCols [Fintype m] (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) (v : m → R) :
    v ᵥ* fromCols B₁ B₂ = Sum.elim (v ᵥ* B₁) (v ᵥ* B₂) := by
  ext (_ | _) <;> rfl

@[deprecated (since := "2024-12-11")] alias vecMul_fromColumns := vecMul_fromCols

@[simp]
lemma sumElim_vecMul_fromRows [Fintype m₁] [Fintype m₂] (B₁ : Matrix m₁ n R) (B₂ : Matrix m₂ n R)
    (v₁ : m₁ → R) (v₂ : m₂ → R) :
    Sum.elim v₁ v₂ ᵥ* fromRows B₁ B₂ = v₁ ᵥ* B₁ + v₂ ᵥ* B₂ := by
  ext
  simp [Matrix.vecMul, fromRows, dotProduct]

@[deprecated (since := "2025-02-21")] alias sum_elim_vecMul_fromRows := sumElim_vecMul_fromRows

@[simp]
lemma fromCols_mulVec_sumElim [Fintype n₁] [Fintype n₂]
    (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (v₁ : n₁ → R) (v₂ : n₂ → R) :
    fromCols A₁ A₂ *ᵥ Sum.elim v₁ v₂ = A₁ *ᵥ v₁ + A₂ *ᵥ v₂ := by
  ext
  simp [Matrix.mulVec, fromCols]

@[deprecated (since := "2025-02-21")] alias fromCols_mulVec_sum_elim := fromCols_mulVec_sumElim
@[deprecated (since := "2024-12-11")] alias fromColumns_mulVec_sum_elim := fromCols_mulVec_sumElim


@[simp]
lemma fromRows_mul [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B : Matrix n m R) :
    fromRows A₁ A₂ * B = fromRows (A₁ * B) (A₂ * B) := by
  ext (_ | _) _ <;> simp [mul_apply]

@[simp]
lemma mul_fromCols [Fintype n] (A : Matrix m n R) (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    A * fromCols B₁ B₂ = fromCols (A * B₁) (A * B₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

@[deprecated (since := "2024-12-11")] alias mul_fromColumns := mul_fromCols

@[simp]
lemma fromRows_zero : fromRows (0 : Matrix m₁ n R) (0 : Matrix m₂ n R) = 0 := by
  ext (_ | _) _ <;> simp

@[simp]
lemma fromCols_zero : fromCols (0 : Matrix m n₁ R) (0 : Matrix m n₂ R) = 0 := by
  ext _ (_ | _) <;> simp

@[deprecated (since := "2024-12-11")] alias fromColumns_zero := fromCols_zero

/-- A row partitioned matrix multiplied by a column partitioned matrix gives a 2 by 2 block
matrix. -/
lemma fromRows_mul_fromCols [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
    (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    (fromRows A₁ A₂) * (fromCols B₁ B₂) =
      fromBlocks (A₁ * B₁) (A₁ * B₂) (A₂ * B₁) (A₂ * B₂) := by
  ext (_ | _) (_ | _) <;> simp

@[deprecated (since := "2024-12-11")] alias fromRows_mul_fromColumns := fromRows_mul_fromCols

/-- A column partitioned matrix multiplied by a row partitioned matrix gives the sum of the "outer"
products of the block matrices. -/
lemma fromCols_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
    (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = (A₁ * B₁ + A₂ * B₂) := by
  ext
  simp [mul_apply]

@[deprecated (since := "2024-12-11")] alias fromColumns_mul_fromRows := fromCols_mul_fromRows

/-- A column partitioned matrix multipiled by a block matrix results in a column partitioned
matrix. -/
lemma fromCols_mul_fromBlocks [Fintype m₁] [Fintype m₂] (A₁ : Matrix m m₁ R) (A₂ : Matrix m m₂ R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    (fromCols A₁ A₂) * fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      fromCols (A₁ * B₁₁ + A₂ * B₂₁) (A₁ * B₁₂ + A₂ * B₂₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

@[deprecated (since := "2024-12-11")] alias fromColumns_mul_fromBlocks := fromCols_mul_fromBlocks

/-- A block matrix multiplied by a row partitioned matrix gives a row partitioned matrix. -/
lemma fromBlocks_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ * (fromRows A₁ A₂) =
      fromRows (B₁₁ * A₁ + B₁₂ * A₂) (B₂₁ * A₁ + B₂₂ * A₂) := by
  ext (_ | _) _ <;> simp [mul_apply]

end Semiring

section CommRing

variable [CommRing R]

/-- Multiplication of a matrix by its inverse is commutative.
This is the column and row partitioned matrix form of `Matrix.mul_eq_one_comm`.

The condition `e : n ≃ n₁ ⊕ n₂` states that `fromCols A₁ A₂` and `fromRows B₁ B₂` are "square".
-/
lemma fromCols_mul_fromRows_eq_one_comm
    [Fintype n₁] [Fintype n₂] [Fintype n] [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂]
    (e : n ≃ n₁ ⊕ n₂)
    (A₁ : Matrix n n₁ R) (A₂ : Matrix n n₂ R) (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromCols A₁ A₂ = 1 :=
  mul_eq_one_comm_of_equiv e

@[deprecated (since := "2024-12-11")]
alias fromColumns_mul_fromRows_eq_one_comm := fromCols_mul_fromRows_eq_one_comm

/-- The lemma `fromCols_mul_fromRows_eq_one_comm` specialized to the case where the index sets
`n₁` and `n₂`, are the result of subtyping by a predicate and its complement. -/
lemma equiv_compl_fromCols_mul_fromRows_eq_one_comm
    [Fintype n] [DecidableEq n] (p : n → Prop) [DecidablePred p]
    (A₁ : Matrix n {i // p i} R) (A₂ : Matrix n {i // ¬p i} R)
    (B₁ : Matrix {i // p i} n R) (B₂ : Matrix {i // ¬p i} n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromCols A₁ A₂ = 1 :=
  fromCols_mul_fromRows_eq_one_comm (id (Equiv.sumCompl p).symm) A₁ A₂ B₁ B₂

@[deprecated (since := "2024-12-11")]
alias equiv_compl_fromColumns_mul_fromRows_eq_one_comm :=
  equiv_compl_fromCols_mul_fromRows_eq_one_comm

end CommRing

section Star
variable [Star R]

/-- A column partitioned matrix in a Star ring when conjugate transposed gives a row partitioned
matrix with the columns of the initial matrix conjugate transposed to become rows. -/
lemma conjTranspose_fromCols_eq_fromRows_conjTranspose (A₁ : Matrix m n₁ R)
    (A₂ : Matrix m n₂ R) :
    conjTranspose (fromCols A₁ A₂) = fromRows (conjTranspose A₁) (conjTranspose A₂) := by
  ext (_ | _) _ <;> simp

@[deprecated (since := "2024-12-11")]
alias conjTranspose_fromColumns_eq_fromRows_conjTranspose :=
  conjTranspose_fromCols_eq_fromRows_conjTranspose

/-- A row partitioned matrix in a Star ring when conjugate transposed gives a column partitioned
matrix with the rows of the initial matrix conjugate transposed to become columns. -/
lemma conjTranspose_fromRows_eq_fromCols_conjTranspose (A₁ : Matrix m₁ n R)
    (A₂ : Matrix m₂ n R) : conjTranspose (fromRows A₁ A₂) =
      fromCols (conjTranspose A₁) (conjTranspose A₂) := by
  ext _ (_ | _) <;> simp

@[deprecated (since := "2024-12-11")]
alias conjTranspose_fromRows_eq_fromColumns_conjTranspose :=
  conjTranspose_fromRows_eq_fromCols_conjTranspose

end Star

end Matrix
