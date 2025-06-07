/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

/-!
# Hadamard product of matrices

This file defines the Hadamard product `Matrix.hadamard`
and contains basic properties about them.

## Main definition

- `Matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `Matrix.hadamard`;

## References

* <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/


variable {α m n R : Type*}

namespace Matrix

/-- `Matrix.hadamard` (denoted as `⊙` within the Matrix namespace) defines the Hadamard product,
    which is the pointwise product of two matrices of the same size. -/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j

-- TODO: set as an equation lemma for `hadamard`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

-- commutativity
theorem hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _

-- associativity
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _

-- distributivity
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _

theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _

-- scalar multiplication
section Scalar

@[simp]
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => mul_zero _

@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => zero_mul _

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]
variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i := by
  ext i j
  by_cases h : i = j <;> simp [h]

end One

section single

variable [DecidableEq m] [DecidableEq n] [MulZeroClass α]

theorem single_hadamard_single_eq (i : m) (j : n) (a b : α) :
    single i j a ⊙ single i j b = single i j (a * b) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

@[deprecated (since := "2025-05-05")]
alias stdBasisMatrix_hadamard_stdBasisMatrix_eq := single_hadamard_single_eq

theorem single_hadamard_single_of_ne
    {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia = ib ∧ ja = jb)) (a b : α) :
    single ia ja a ⊙ single ib jb b = 0 := by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

end single

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

end Diagonal

section trace

variable [Fintype m] [Fintype n]
variable (R) [Semiring α]

theorem sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ) :=
  rfl

theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    v ᵥ* (A ⊙ B) ⬝ᵥ w = trace (diagonal v * A * (B * diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]

end trace

end BasicProperties

end Matrix
