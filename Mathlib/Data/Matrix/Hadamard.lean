/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathlib.LinearAlgebra.Matrix.Trace

#align_import data.matrix.hadamard from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

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


variable {α β γ m n : Type*}
variable {R : Type*}

namespace Matrix

open Matrix

/-- `Matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size. -/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j
#align matrix.hadamard Matrix.hadamard

-- TODO: set as an equation lemma for `hadamard`, see mathlib4#3024
@[simp]
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl
#align matrix.hadamard_apply Matrix.hadamard_apply

scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

-- commutativity
theorem hadamard_comm [CommSemigroup α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _
#align matrix.hadamard_comm Matrix.hadamard_comm

-- associativity
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _
#align matrix.hadamard_assoc Matrix.hadamard_assoc

-- distributivity
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _
#align matrix.hadamard_add Matrix.hadamard_add

theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _
#align matrix.add_hadamard Matrix.add_hadamard

-- scalar multiplication
section Scalar

@[simp]
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _
#align matrix.smul_hadamard Matrix.smul_hadamard

@[simp]
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _
#align matrix.hadamard_smul Matrix.hadamard_smul

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => mul_zero _
#align matrix.hadamard_zero Matrix.hadamard_zero

@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => zero_mul _
#align matrix.zero_hadamard Matrix.zero_hadamard

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]
variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i := by
  ext i j
  by_cases h: i = j <;> simp [h]
#align matrix.hadamard_one Matrix.hadamard_one

theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i := by
  ext i j
  by_cases h : i = j <;> simp [h]
#align matrix.one_hadamard Matrix.one_hadamard

end One

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)
#align matrix.diagonal_hadamard_diagonal Matrix.diagonal_hadamard_diagonal

end Diagonal

section trace

variable [Fintype m] [Fintype n]
variable (R) [Semiring α] [Semiring R] [Module R α]

theorem sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ) :=
  rfl
#align matrix.sum_hadamard_eq Matrix.sum_hadamard_eq

theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dotProduct (v ᵥ* (A ⊙ B)) w = trace (diagonal v * A * (B * diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]
#align matrix.dot_product_vec_mul_hadamard Matrix.dotProduct_vecMul_hadamard

end trace

end BasicProperties

end Matrix
