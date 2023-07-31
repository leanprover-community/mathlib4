/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Block Matrices from Rows and Columns

This file provides the basic definitions of matrices composed from columns and rows.
The concatenation of two matrices with the same row indices can be expressed as
`A = fromColumns A₁ A₂` the concatenation of two matrices with the same column indices
can be expressed as `B = fromRows B₁ B₂`.

We then provide a few lemmas that deal with the products of these with each other and
with block matrices

## Tags
column matrices, row matrices, column row block matrices
-/

namespace Matrix

variable {R : Type _}
variable {M M₁ M₂ N N₁ N₂ : Type _}
variable [Fintype M] [Fintype M₁] [Fintype M₂]
variable [Fintype N] [Fintype N₁] [Fintype N₂]
variable [DecidableEq M] [DecidableEq M₁] [DecidableEq M₂]
variable [DecidableEq N] [DecidableEq N₁] [DecidableEq N₂]

/-- Concatenate together two matrices A₁[M₁ × N] and A₂[M₂ × N] with the same columns (N) to get a
bigger matrix indexed by [(M₁ ⊕ M₂) × N] -/
def fromRows (A₁ : Matrix M₁ N R) (A₂ : Matrix M₂ N R) : Matrix (M₁ ⊕ M₂) N R :=
  of (Sum.elim A₁ A₂)

/-- Concatenate together two matrices B₁[M × N₁] and B₂[M × N₂] with the same rows (M) to get a
bigger matrix indexed by [M × (N₁ ⊕ N₂)] -/
def fromColumns (B₁ : Matrix M N₁ R) (B₂ : Matrix M N₂ R) : Matrix M (N₁ ⊕ N₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

/-- Given a column partitioned matrix extract the first column -/
def toColumns₁ (A : Matrix M (N₁ ⊕ N₂) R) : Matrix M N₁ R := of fun i j => (A i (Sum.inl j))

/-- Given a column partitioned matrix extract the second column -/
def toColumns₂ (A : Matrix M (N₁ ⊕ N₂) R) : Matrix M N₂ R := of fun i j => (A i (Sum.inr j))

/-- Given a row partitioned matrix extract the first row -/
def toRows₁ (A : Matrix (M₁ ⊕ M₂) N R) : Matrix M₁ N R := of fun i j => (A (Sum.inl i) j)

/-- Given a row partitioned matrix extract the second row -/
def toRows₂ (A : Matrix (M₁ ⊕ M₂) N R) : Matrix M₂ N R := of fun i j => (A (Sum.inr i) j)

@[simp]
lemma fromColumns_toColumns (A : Matrix M (N₁ ⊕ N₂) R) :
    fromColumns A.toColumns₁ A.toColumns₂ = A := by
  unfold fromColumns toColumns₁ toColumns₂
  funext i j
  cases' j
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr])

lemma fromColumns_ext_iff (A₁ : Matrix M N₁ R) (A₂ : Matrix M N₂ R) (B₁ : Matrix M N₁ R)
    (B₂ : Matrix M N₂ R) :
    fromColumns A₁ A₂ = fromColumns B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by
  simp_rw [fromColumns, ← Matrix.ext_iff, of_apply, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  exact ⟨(fun h => ⟨fun i j => (h i).1 j, fun _ _ => (h _).2 _⟩),
    (fun h => (fun _ => ⟨(h.1 _), (h.2 _)⟩))⟩

lemma fromRows_toRows (A : Matrix (M₁ ⊕ M₂) N R) : A = fromRows A.toRows₁ A.toRows₂ := by
  unfold fromRows toRows₁ toRows₂
  funext i j
  cases' i
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr])

lemma fromRows_ext_iff (A₁ : Matrix M₁ N R) (A₂ : Matrix M₂ N R) (B₁ : Matrix M₁ N R)
    (B₂ : Matrix M₂ N R) : fromRows A₁ A₂ = fromRows B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by
  simp_rw [fromRows, ← Matrix.ext_iff, of_apply, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/- A column partioned matrix when transposed gives a row partioned matrix with columns of the
initial matrix tranposed to become rows. -/
lemma transpose_fromColumns (A₁ : Matrix M N₁ R) (A₂ : Matrix M N₂ R) :
    transpose (fromColumns A₁ A₂) = fromRows (transpose A₁) (transpose A₂) := by
  rw [fromColumns, fromRows]
  funext i j
  cases' i with i i
  all_goals (simp only [transpose_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

/- A row partioned matrix when transposed gives a column partioned matrix with rows of the initial
matrix tranposed to become columns. -/
lemma transpose_fromRows_eq_fromColumns_transpose (A₁ : Matrix M₁ N R) (A₂ : Matrix M₂ N R) :
    transpose (fromRows A₁ A₂) = fromColumns (transpose A₁) (transpose A₂) := by
  rw [fromColumns, fromRows]
  funext i j
  cases' j with j j
  all_goals (simp only [transpose_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

section Semiring

variable [Semiring R]

lemma fromRows_mul (A₁ : Matrix M₁ N R) (A₂ : Matrix M₂ N R) (B : Matrix N M R) :
    (fromRows A₁ A₂) ⬝ B = fromRows (A₁ ⬝ B) (A₂ ⬝ B) := by
  unfold fromRows
  funext i j
  cases' i with i i
  all_goals (simp only [mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

lemma mul_fromColumns (A : Matrix M N R) (B₁ : Matrix N N₁ R) (B₂ : Matrix N N₂ R) :
    A ⬝ (fromColumns B₁ B₂) = fromColumns (A ⬝ B₁) (A ⬝ B₂) := by
  unfold fromColumns
  funext i j
  cases' j with j j
  all_goals (simp only [mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

lemma fromRows_zero : fromRows (0 : Matrix M₁ N R) (0 : Matrix M₂ N R) = 0 := by
  funext i j
  unfold fromRows
  simp only [Sum.elim_zero_zero, of_apply, Pi.zero_apply, zero_apply]

lemma fromColumns_zero : fromColumns (0 : Matrix M N₁ R) (0 : Matrix M N₂ R) = 0 := by
  funext i j
  unfold fromColumns
  cases' j with j j
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr, zero_apply])

/-- A row partitioned matrix multiplied by a column partioned matrix gives a 2 by 2 block matrix -/
lemma fromRows_mul_fromColumns (A₁ : Matrix M₁ N R) (A₂ : Matrix M₂ N R)
    (B₁ : Matrix N N₁ R) (B₂ : Matrix N N₂ R) :
    (fromRows A₁ A₂) ⬝ (fromColumns B₁ B₂) = fromBlocks (A₁ ⬝ B₁) (A₁ ⬝ B₂) (A₂ ⬝ B₁) (A₂ ⬝ B₂) := by
  funext i j
  rw [fromRows, fromColumns]
  cases i;
  all_goals (cases j)
  all_goals (simp only [
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

/-- A column partitioned matrix mulitplied by a row partitioned matrix gives the sum of the "outer"
products of the block matrices -/
lemma fromColumns_mul_fromRows (A₁ : Matrix M N₁ R) (A₂ : Matrix M N₂ R)
    (B₁ : Matrix N₁ N R) (B₂ : Matrix N₂ N R) :
    fromColumns A₁ A₂ ⬝ fromRows B₁ B₂ = (A₁ ⬝ B₁ + A₂ ⬝ B₂) := by
  funext i j
  rw [fromRows, fromColumns]
  simp only [add_apply, mul_apply, of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- A column partitioned matrix multipiled by a block matrix results in a column partioned matrix -/
lemma fromColumns_mul_fromBlocks (A₁ : Matrix M M₁ R) (A₂ : Matrix M M₂ R)
    (B₁₁ : Matrix M₁ N₁ R) (B₁₂ : Matrix M₁ N₂ R) (B₂₁ : Matrix M₂ N₁ R) (B₂₂ : Matrix M₂ N₂ R) :
    (fromColumns A₁ A₂) ⬝ fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      fromColumns (A₁ ⬝ B₁₁ + A₂ ⬝ B₂₁) (A₁ ⬝ B₁₂ + A₂ ⬝ B₂₂) := by
  funext i j
  rw [fromColumns, fromColumns, fromBlocks]
  cases j
  all_goals simp only [of_apply, add_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_apply]

/-- A block matrix mulitplied by a row partitioned matrix gives a row partitioned matrix -/
lemma fromBlocks_mul_fromRows (A₁ : Matrix N₁ N R) (A₂ : Matrix N₂ N R)
    (B₁₁ : Matrix M₁ N₁ R) (B₁₂ : Matrix M₁ N₂ R) (B₂₁ : Matrix M₂ N₁ R) (B₂₂ : Matrix M₂ N₂ R) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ ⬝ (fromRows A₁ A₂) =
      fromRows (B₁₁ ⬝ A₁ + B₁₂ ⬝ A₂) (B₂₁ ⬝ A₁ + B₂₂ ⬝ A₂) := by
  funext i j
  rw [fromRows, fromRows, fromBlocks]
  cases i
  all_goals simp only [of_apply, add_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_apply]

end Semiring

section CommRing

variable [CommRing R]

/-- Multiplication of a matrix by its inverse is commutative.
This is the column and row partitioned matrix form of `Matrix.mul_eq_one_comm`.

The condition `e : N ≃ N₁ ⊕ N₂` states that `fromColumns A₁ A₂` and `fromRows B₁ B₂` are "square".
-/
lemma fromColumns_mul_fromRows_eq_one_comm (e : N ≃ N₁ ⊕ N₂)
    (A₁ : Matrix N N₁ R) (A₂ : Matrix N N₂ R) (B₁ : Matrix N₁ N R) (B₂ : Matrix N₂ N R) :
    fromColumns A₁ A₂ ⬝ fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ ⬝ fromColumns A₁ A₂ = 1 := by
  constructor
  intro h
  rw [← Matrix.submatrix_id_id (fromRows B₁ B₂ ⬝ fromColumns A₁ A₂),
    ← Matrix.submatrix_mul_equiv (fromRows B₁ B₂) (fromColumns A₁ A₂) _ e.symm _]
  swap
  intro h
  rw [← Matrix.submatrix_id_id (fromColumns A₁ A₂ ⬝ fromRows B₁ B₂),
    ← Matrix.submatrix_mul_equiv (fromColumns A₁ A₂) (fromRows B₁ B₂) _ e _]
  all_goals
  ( rw [mul_eq_one_comm, ← Matrix.submatrix_mul, h, submatrix_one_equiv]
    exact Function.bijective_id )

/- The lemma `fromColumns_mul_fromRows_eq_one_comm` specialized to the case where the index sets N₁
and N₂, are the result of subtyping by a predicate and its complement. -/
lemma equiv_compl_fromColumns_mul_fromRows_eq_one_comm (p : N → Prop)[DecidablePred p]
    (A₁ : Matrix N {i // p i} R) (A₂ : Matrix N {i // ¬p i} R)
    (B₁ : Matrix {i // p i} N R) (B₂ : Matrix {i // ¬p i} N R) :
    fromColumns A₁ A₂ ⬝ fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ ⬝ fromColumns A₁ A₂ = 1 :=
  fromColumns_mul_fromRows_eq_one_comm (id (Equiv.sumCompl p).symm) A₁ A₂ B₁ B₂

end CommRing

section Star
variable [Star R]
/- A column partioned matrix in a Star ring when conjugate transposed gives a row partitioned matrix
with the columns of the initial matrix conjugate transposed to become rows. -/
lemma conjTranspose_fromColumns_eq_fromRows_conjTranspose (A₁ : Matrix M N₁ R)
    (A₂ : Matrix M N₂ R) : conjTranspose (fromColumns A₁ A₂) =
      fromRows (conjTranspose A₁) (conjTranspose A₂) := by
  rw [fromColumns, fromRows]
  funext i j
  cases' i with i i
  all_goals (simp only [conjTranspose_apply, of_apply, Sum.elim_inl, Sum.elim_inr])

/- A row partioned matrix in a Star ring when conjugate transposed gives a column partitioned matrix
with the rows of the initial matrix conjugate transposed to become columns. -/
lemma conjTranspose_fromRows_eq_fromColumns_conjTranspose (A₁ : Matrix M₁ N R)
    (A₂ : Matrix M₂ N R) : conjTranspose (fromRows A₁ A₂) =
      fromColumns (conjTranspose A₁) (conjTranspose A₂) := by
  rw [fromColumns, fromRows]
  funext j i
  cases' i with i i
  all_goals (simp only [conjTranspose_apply, of_apply, Sum.elim_inl, Sum.elim_inr])

end Star

end Matrix
