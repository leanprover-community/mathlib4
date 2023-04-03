/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser, Oliver Nash

! This file was ported from Lean 3 source module data.matrix.basis
! leanprover-community/mathlib commit 320df450e9abeb5fc6417971e75acb6ae8bc3794
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Matrices with a single non-zero element.

This file provides `matrix.std_basis_matrix`. The matrix `matrix.std_basis_matrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/


variable {l m n : Type _}

variable {R α : Type _}

namespace Matrix

open Matrix

open BigOperators

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Semiring α]

/-- `std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α := fun i' j' =>
  if i = i' ∧ j = j' then a else 0
#align matrix.std_basis_matrix Matrix.stdBasisMatrix

@[simp]
theorem smul_stdBasisMatrix (i : m) (j : n) (a b : α) :
    b • stdBasisMatrix i j a = stdBasisMatrix i j (b • a) :=
  by
  unfold std_basis_matrix
  ext
  simp
#align matrix.smul_std_basis_matrix Matrix.smul_stdBasisMatrix

@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 :=
  by
  unfold std_basis_matrix
  ext
  simp
#align matrix.std_basis_matrix_zero Matrix.stdBasisMatrix_zero

theorem stdBasisMatrix_add (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b :=
  by
  unfold std_basis_matrix; ext
  split_ifs with h <;> simp [h]
#align matrix.std_basis_matrix_add Matrix.stdBasisMatrix_add

theorem matrix_eq_sum_std_basis [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ (i : m) (j : n), stdBasisMatrix i j (x i j) :=
  by
  ext; symm
  iterate 2 rw [Finset.sum_apply]
  convert Fintype.sum_eq_single i _
  · simp [std_basis_matrix]
  · intro j hj
    simp [std_basis_matrix, hj]
#align matrix.matrix_eq_sum_std_basis Matrix.matrix_eq_sum_std_basis

-- TODO: tie this up with the `basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one
-- TODO: add `std_basis_vec`
theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
    stdBasisMatrix i j 1 = vecMulVec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 :=
  by
  ext
  norm_num [std_basis_matrix, vec_mul_vec]
  exact ite_and _ _ _ _
#align matrix.std_basis_eq_basis_mul_basis Matrix.std_basis_eq_basis_mul_basis

-- todo: the old proof used fintypes, I don't know `finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on' [Fintype m] [Fintype n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M :=
  by
  rw [matrix_eq_sum_std_basis M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis
#align matrix.induction_on' Matrix.induction_on'

@[elab_as_elim]
protected theorem induction_on [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (stdBasisMatrix i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis
#align matrix.induction_on Matrix.induction_on

namespace StdBasisMatrix

section

variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
theorem apply_same : stdBasisMatrix i j c i j = c :=
  if_pos (And.intro rfl rfl)
#align matrix.std_basis_matrix.apply_same Matrix.stdBasisMatrix.apply_same

@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 :=
  by
  simp only [std_basis_matrix, and_imp, ite_eq_right_iff]
  tauto
#align matrix.std_basis_matrix.apply_of_ne Matrix.stdBasisMatrix.apply_of_ne

@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]
#align matrix.std_basis_matrix.apply_of_row_ne Matrix.stdBasisMatrix.apply_of_row_ne

@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]
#align matrix.std_basis_matrix.apply_of_col_ne Matrix.stdBasisMatrix.apply_of_col_ne

end

section

variable (i j : n) (c : α) (i' j' : n)

@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun k => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)
#align matrix.std_basis_matrix.diag_zero Matrix.stdBasisMatrix.diag_zero

@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c :=
  by
  ext j
  by_cases hij : i = j <;> try rw [hij] <;> simp [hij]
#align matrix.std_basis_matrix.diag_same Matrix.stdBasisMatrix.diag_same

variable [Fintype n]

@[simp]
theorem trace_zero (h : j ≠ i) : trace (stdBasisMatrix i j c) = 0 := by simp [trace, h]
#align matrix.std_basis_matrix.trace_zero Matrix.stdBasisMatrix.trace_zero

@[simp]
theorem trace_eq : trace (stdBasisMatrix i i c) = c := by simp [trace]
#align matrix.std_basis_matrix.trace_eq Matrix.stdBasisMatrix.trace_eq

@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) i b = c * M j b := by simp [mul_apply, std_basis_matrix]
#align matrix.std_basis_matrix.mul_left_apply_same Matrix.stdBasisMatrix.mul_left_apply_same

@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, std_basis_matrix, mul_comm]
#align matrix.std_basis_matrix.mul_right_apply_same Matrix.stdBasisMatrix.mul_right_apply_same

@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) a b = 0 := by simp [mul_apply, h.symm]
#align matrix.std_basis_matrix.mul_left_apply_of_ne Matrix.stdBasisMatrix.mul_left_apply_of_ne

@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]
#align matrix.std_basis_matrix.mul_right_apply_of_ne Matrix.stdBasisMatrix.mul_right_apply_of_ne

@[simp]
theorem mul_same (k : n) (d : α) :
    stdBasisMatrix i j c ⬝ stdBasisMatrix j k d = stdBasisMatrix i k (c * d) :=
  by
  ext (a b)
  simp only [mul_apply, std_basis_matrix, boole_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]
#align matrix.std_basis_matrix.mul_same Matrix.stdBasisMatrix.mul_same

@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) : stdBasisMatrix i j c ⬝ stdBasisMatrix k l d = 0 :=
  by
  ext (a b)
  simp only [mul_apply, boole_mul, std_basis_matrix]
  by_cases h₁ : i = a <;> simp [h₁, h, h.symm]
#align matrix.std_basis_matrix.mul_of_ne Matrix.stdBasisMatrix.mul_of_ne

end

end StdBasisMatrix

end Matrix

