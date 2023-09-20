/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser, Oliver Nash
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

#align_import data.matrix.basis from "leanprover-community/mathlib"@"320df450e9abeb5fc6417971e75acb6ae8bc3794"

/-!
# Matrices with a single non-zero element.

This file provides `matrix.stdBasisMatrix`. The matrix `matrix.stdBasisMatrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/


variable {l m n : Type*}

variable {R α : Type*}

namespace Matrix

open Matrix

open BigOperators

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Semiring α]

/-- `stdBasisMatrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α := fun i' j' =>
  if i = i' ∧ j = j' then a else 0
#align matrix.std_basis_matrix Matrix.stdBasisMatrix

@[simp]
theorem smul_stdBasisMatrix (i : m) (j : n) (a b : α) :
    b • stdBasisMatrix i j a = stdBasisMatrix i j (b • a) := by
  unfold stdBasisMatrix
  ext
  simp
#align matrix.smul_std_basis_matrix Matrix.smul_stdBasisMatrix

@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 := by
  unfold stdBasisMatrix
  ext
  simp
#align matrix.std_basis_matrix_zero Matrix.stdBasisMatrix_zero

theorem stdBasisMatrix_add (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b := by
  unfold stdBasisMatrix; ext
  split_ifs with h <;> simp [h]
#align matrix.std_basis_matrix_add Matrix.stdBasisMatrix_add

theorem matrix_eq_sum_std_basis [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, stdBasisMatrix i j (x i j) := by
  ext i j; symm
  iterate 2 rw [Finset.sum_apply]
  -- Porting note: was `convert`
  refine (Fintype.sum_eq_single i ?_).trans ?_; swap
  · -- Porting note: `simp` seems unwilling to apply `Fintype.sum_apply`
    simp only [stdBasisMatrix]
    rw [Fintype.sum_apply, Fintype.sum_apply]
    simp
  · intro j' hj'
    -- Porting note: `simp` seems unwilling to apply `Fintype.sum_apply`
    simp only [stdBasisMatrix]
    rw [Fintype.sum_apply, Fintype.sum_apply]
    simp [hj']
#align matrix.matrix_eq_sum_std_basis Matrix.matrix_eq_sum_std_basis

-- TODO: tie this up with the `Basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one
-- TODO: add `std_basis_vec`
theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
    stdBasisMatrix i j 1 = vecMulVec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 := by
  ext i' j'
  -- Porting note: was `norm_num [std_basis_matrix, vec_mul_vec]` though there are no numerals
  -- involved.
  simp only [stdBasisMatrix, vecMulVec, mul_ite, mul_one, mul_zero, of_apply]
  -- Porting note: added next line
  simp_rw [@and_comm (i = i')]
  exact ite_and _ _ _ _
#align matrix.std_basis_eq_basis_mul_basis Matrix.std_basis_eq_basis_mul_basis

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on' [Fintype m] [Fintype n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M := by
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
#align matrix.std_basis_matrix.apply_same Matrix.StdBasisMatrix.apply_same

@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 := by
  simp only [stdBasisMatrix, and_imp, ite_eq_right_iff]
  tauto
#align matrix.std_basis_matrix.apply_of_ne Matrix.StdBasisMatrix.apply_of_ne

@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]
#align matrix.std_basis_matrix.apply_of_row_ne Matrix.StdBasisMatrix.apply_of_row_ne

@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]
#align matrix.std_basis_matrix.apply_of_col_ne Matrix.StdBasisMatrix.apply_of_col_ne

end

section

variable (i j : n) (c : α) (i' j' : n)

@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)
#align matrix.std_basis_matrix.diag_zero Matrix.StdBasisMatrix.diag_zero

@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]
#align matrix.std_basis_matrix.diag_same Matrix.StdBasisMatrix.diag_same

variable [Fintype n]

@[simp]
theorem trace_zero (h : j ≠ i) : trace (stdBasisMatrix i j c) = 0 := by
  -- Porting note: added `-diag_apply`
  simp [trace, -diag_apply, h]
#align matrix.std_basis_matrix.trace_zero Matrix.StdBasisMatrix.trace_zero

@[simp]
theorem trace_eq : trace (stdBasisMatrix i i c) = c := by
  -- Porting note: added `-diag_apply`
  simp [trace, -diag_apply]
#align matrix.std_basis_matrix.trace_eq Matrix.StdBasisMatrix.trace_eq

@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) i b = c * M j b := by simp [mul_apply, stdBasisMatrix]
#align matrix.std_basis_matrix.mul_left_apply_same Matrix.StdBasisMatrix.mul_left_apply_same

@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, stdBasisMatrix, mul_comm]
#align matrix.std_basis_matrix.mul_right_apply_same Matrix.StdBasisMatrix.mul_right_apply_same

@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) a b = 0 := by simp [mul_apply, h.symm]
#align matrix.std_basis_matrix.mul_left_apply_of_ne Matrix.StdBasisMatrix.mul_left_apply_of_ne

@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]
#align matrix.std_basis_matrix.mul_right_apply_of_ne Matrix.StdBasisMatrix.mul_right_apply_of_ne

@[simp]
theorem mul_same (k : n) (d : α) :
    stdBasisMatrix i j c ⬝ stdBasisMatrix j k d = stdBasisMatrix i k (c * d) := by
  ext a b
  simp only [mul_apply, stdBasisMatrix, boole_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]
#align matrix.std_basis_matrix.mul_same Matrix.StdBasisMatrix.mul_same

@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) :
    stdBasisMatrix i j c ⬝ stdBasisMatrix k l d = 0 := by
  ext a b
  simp only [mul_apply, boole_mul, stdBasisMatrix]
  by_cases h₁ : i = a
  -- Porting note: was `simp [h₁, h, h.symm]`
  · simp only [h₁, true_and, mul_ite, ite_mul, zero_mul, mul_zero, ← ite_and, zero_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    apply if_neg
    rintro ⟨⟨rfl, rfl⟩, h⟩
    contradiction
  · simp only [h₁, false_and, ite_false, mul_ite, zero_mul, mul_zero, ite_self,
      Finset.sum_const_zero, zero_apply]
#align matrix.std_basis_matrix.mul_of_ne Matrix.StdBasisMatrix.mul_of_ne

end

end StdBasisMatrix

end Matrix
