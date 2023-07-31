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
variable {m m₁ m₂ n n₁ n₂ : Type _}
variable [Fintype m] [Fintype m₁] [Fintype m₂]
variable [Fintype n] [Fintype n₁] [Fintype n₂]
variable [DecidableEq m] [DecidableEq m₁] [DecidableEq m₂]
variable [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂]

/-- Concatenate together two matrices A₁[m₁ × N] and A₂[m₂ × N] with the same columns (N) to get a
bigger matrix indexed by [(m₁ ⊕ m₂) × N] -/
def fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) : Matrix (m₁ ⊕ m₂) n R :=
  of (Sum.elim A₁ A₂)

/-- Concatenate together two matrices B₁[m × n₁] and B₂[m × n₂] with the same rows (M) to get a
bigger matrix indexed by [m × (n₁ ⊕ n₂)] -/
def fromColumns (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) : Matrix m (n₁ ⊕ n₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

/-- Given a column partitioned matrix extract the first column -/
def toColumns₁ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₁ R := of fun i j => (A i (Sum.inl j))

/-- Given a column partitioned matrix extract the second column -/
def toColumns₂ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₂ R := of fun i j => (A i (Sum.inr j))

/-- Given a row partitioned matrix extract the first row -/
def toRows₁ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₁ n R := of fun i j => (A (Sum.inl i) j)

/-- Given a row partitioned matrix extract the second row -/
def toRows₂ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₂ n R := of fun i j => (A (Sum.inr i) j)

@[simp]
lemma fromColumns_toColumns (A : Matrix m (n₁ ⊕ n₂) R) :
    fromColumns A.toColumns₁ A.toColumns₂ = A := by
  unfold fromColumns toColumns₁ toColumns₂
  funext i j
  cases' j
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr])

@[simp]
lemma fromRows_toRows (A : Matrix (m₁ ⊕ m₂) n R) : fromRows A.toRows₁ A.toRows₂ = A := by
  unfold fromRows toRows₁ toRows₂
  funext i j
  cases' i
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr])

lemma fromRows_inj : Function.Injective2 (@fromRows R m₁ m₂ n) := by
  intros x1 x2 y1 y2
  unfold fromRows
  simp_rw [Function.funext_iff, ← Matrix.ext_iff, EmbeddingLike.apply_eq_iff_eq,
    of_apply, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  exact (fun h => ⟨ fun _ _ => h.1 _ _ , fun _ _ => h.2 _ _ ⟩)

lemma fromColumns_inj : Function.Injective2 (@fromColumns R m n₁ n₂) := by
  intros x1 x2 y1 y2
  unfold fromColumns
  simp_rw [Function.funext_iff, ← Matrix.ext_iff, EmbeddingLike.apply_eq_iff_eq,
    of_apply, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  exact (fun h => ⟨fun _ _ => (h _).1 _, fun _ _ => (h _).2 _⟩)

lemma fromColumns_ext_iff (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (B₁ : Matrix m n₁ R)
    (B₂ : Matrix m n₂ R) :
    fromColumns A₁ A₂ = fromColumns B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromColumns_inj.eq_iff

lemma fromRows_ext_iff (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B₁ : Matrix m₁ n R)
    (B₂ : Matrix m₂ n R) :
    fromRows A₁ A₂ = fromRows B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromRows_inj.eq_iff

@[simp]
lemma fromRows_apply_inl (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₁) (j : n) :
    (fromRows A₁ A₂) (Sum.inl i) j = A₁ i j := by
  unfold fromRows
  simp only [of_apply, Sum.elim_inl]

@[simp]
lemma fromRows_apply_inr (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₂) (j : n) :
    (fromRows A₁ A₂) (Sum.inr i) j = A₂ i j := by
  unfold fromRows
  simp only [of_apply, Sum.elim_inr]

@[simp]
lemma fromColumns_apply_inl (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₁) :
    (fromColumns A₁ A₂) i (Sum.inl j) = A₁ i j := by
  unfold fromColumns
  simp only [of_apply, Sum.elim_inl]

@[simp]
lemma fromColumns_apply_inr (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₂) :
    (fromColumns A₁ A₂) i (Sum.inr j) = A₂ i j := by
  unfold fromColumns
  simp only [of_apply, Sum.elim_inr]

/- A column partioned matrix when transposed gives a row partioned matrix with columns of the
initial matrix tranposed to become rows. -/
lemma transpose_fromColumns (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    transpose (fromColumns A₁ A₂) = fromRows (transpose A₁) (transpose A₂) := by
  funext i j
  cases' i with i i
  all_goals (simp only [transpose_apply, fromColumns_apply_inl, fromRows_apply_inl,
    fromColumns_apply_inr, fromRows_apply_inr])

/- A row partioned matrix when transposed gives a column partioned matrix with rows of the initial
matrix tranposed to become columns. -/
lemma transpose_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    transpose (fromRows A₁ A₂) = fromColumns (transpose A₁) (transpose A₂) := by
  funext i j
  cases' j with j j
  all_goals (simp only [transpose_apply, fromRows_apply_inl, fromColumns_apply_inl,
    fromColumns_apply_inr, fromRows_apply_inr])

section Semiring

variable [Semiring R]
/- The proofs are "shorter" with the unfolds instead of the simp lemmas above so I will continue
with them for the next lemmas -/
@[simp]
lemma fromRows_mul (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B : Matrix n m R) :
    (fromRows A₁ A₂) ⬝ B = fromRows (A₁ ⬝ B) (A₂ ⬝ B) := by
  unfold fromRows
  funext i j
  cases' i with i i
  all_goals (simp only [mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

@[simp]
lemma mul_fromColumns (A : Matrix m n R) (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    A ⬝ (fromColumns B₁ B₂) = fromColumns (A ⬝ B₁) (A ⬝ B₂) := by
  unfold fromColumns
  funext i j
  cases' j with j j
  all_goals (simp only [mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

@[simp]
lemma fromRows_zero : fromRows (0 : Matrix m₁ n R) (0 : Matrix m₂ n R) = 0 := by
  funext i j
  unfold fromRows
  simp only [Sum.elim_zero_zero, of_apply, Pi.zero_apply, zero_apply]

@[simp]
lemma fromColumns_zero : fromColumns (0 : Matrix m n₁ R) (0 : Matrix m n₂ R) = 0 := by
  funext i j
  unfold fromColumns
  cases' j with j j
  all_goals (simp only [of_apply, Sum.elim_inl, Sum.elim_inr, zero_apply])

@[simp]
lemma fromColumns_fromRows_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromColumns (fromRows B₁₁ B₂₁) (fromRows B₁₂ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
    unfold fromRows fromColumns
    funext i j
    cases' i with i i
    all_goals (
      cases' j with j j;
      all_goals ( simp only [of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] ) )

@[simp]
lemma fromRows_fromColumn_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromRows (fromColumns B₁₁ B₁₂) (fromColumns B₂₁ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
    unfold fromRows fromColumns
    funext i j
    cases' i with i i
    all_goals (
      cases' j with j j;
      all_goals ( simp only [of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] ) )

/-- A row partitioned matrix multiplied by a column partioned matrix gives a 2 by 2 block matrix -/
lemma fromRows_mul_fromColumns (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
    (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) : (fromRows A₁ A₂) ⬝ (fromColumns B₁ B₂) =
      fromBlocks (A₁ ⬝ B₁) (A₁ ⬝ B₂) (A₂ ⬝ B₁) (A₂ ⬝ B₂) := by
  funext i j
  rw [fromRows, fromColumns]
  cases i;
  all_goals (cases j)
  all_goals (simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, mul_apply, of_apply, Sum.elim_inl, Sum.elim_inr] )

/-- A column partitioned matrix mulitplied by a row partitioned matrix gives the sum of the "outer"
products of the block matrices -/
lemma fromColumns_mul_fromRows (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
    (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromColumns A₁ A₂ ⬝ fromRows B₁ B₂ = (A₁ ⬝ B₁ + A₂ ⬝ B₂) := by
  funext i j
  rw [fromRows, fromColumns]
  simp only [add_apply, mul_apply, of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- A column partitioned matrix multipiled by a block matrix results in a column partioned matrix -/
lemma fromColumns_mul_fromBlocks (A₁ : Matrix m m₁ R) (A₂ : Matrix m m₂ R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    (fromColumns A₁ A₂) ⬝ fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      fromColumns (A₁ ⬝ B₁₁ + A₂ ⬝ B₂₁) (A₁ ⬝ B₁₂ + A₂ ⬝ B₂₂) := by
  funext i j
  rw [fromColumns, fromColumns, fromBlocks]
  cases j
  all_goals simp only [of_apply, add_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_apply]

/-- A block matrix mulitplied by a row partitioned matrix gives a row partitioned matrix -/
lemma fromBlocks_mul_fromRows (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
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

The condition `e : n ≃ n₁ ⊕ n₂` states that `fromColumns A₁ A₂` and `fromRows B₁ B₂` are "square".
-/
lemma fromColumns_mul_fromRows_eq_one_comm (e : n ≃ n₁ ⊕ n₂)
    (A₁ : Matrix n n₁ R) (A₂ : Matrix n n₂ R) (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
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

/- The lemma `fromColumns_mul_fromRows_eq_one_comm` specialized to the case where the index sets n₁
and n₂, are the result of subtyping by a predicate and its complement. -/
lemma equiv_compl_fromColumns_mul_fromRows_eq_one_comm (p : n → Prop)[DecidablePred p]
    (A₁ : Matrix n {i // p i} R) (A₂ : Matrix n {i // ¬p i} R)
    (B₁ : Matrix {i // p i} n R) (B₂ : Matrix {i // ¬p i} n R) :
    fromColumns A₁ A₂ ⬝ fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ ⬝ fromColumns A₁ A₂ = 1 :=
  fromColumns_mul_fromRows_eq_one_comm (id (Equiv.sumCompl p).symm) A₁ A₂ B₁ B₂

end CommRing

section Star
variable [Star R]
/- A column partioned matrix in a Star ring when conjugate transposed gives a row partitioned matrix
with the columns of the initial matrix conjugate transposed to become rows. -/
lemma conjTranspose_fromColumns_eq_fromRows_conjTranspose (A₁ : Matrix m n₁ R)
    (A₂ : Matrix m n₂ R) : conjTranspose (fromColumns A₁ A₂) =
      fromRows (conjTranspose A₁) (conjTranspose A₂) := by
  rw [fromColumns, fromRows]
  funext i j
  cases' i with i i
  all_goals (simp only [conjTranspose_apply, of_apply, Sum.elim_inl, Sum.elim_inr])

/- A row partioned matrix in a Star ring when conjugate transposed gives a column partitioned matrix
with the rows of the initial matrix conjugate transposed to become columns. -/
lemma conjTranspose_fromRows_eq_fromColumns_conjTranspose (A₁ : Matrix m₁ n R)
    (A₂ : Matrix m₂ n R) : conjTranspose (fromRows A₁ A₂) =
      fromColumns (conjTranspose A₁) (conjTranspose A₂) := by
  rw [fromColumns, fromRows]
  funext j i
  cases' i with i i
  all_goals (simp only [conjTranspose_apply, of_apply, Sum.elim_inl, Sum.elim_inr])

end Star

end Matrix
