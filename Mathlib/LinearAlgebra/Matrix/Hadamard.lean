/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic

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

@[expose] public section


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

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

theorem hadamard_diagonal (M) (w : n → α) :
    M ⊙ diagonal w = diagonal (M.diag * w) := by aesop (add simp diagonal)

theorem diagonal_hadamard (M) (w : n → α) :
    diagonal w ⊙ M = diagonal (w * M.diag) := by aesop (add simp diagonal)

theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) := by simp [diagonal_hadamard]

theorem diagonal_hadamard_eq_diagonal_iff {A : Matrix n n α} {d e} :
    diagonal d ⊙ A = diagonal e ↔ d * A.diag = e := by
  simp [diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]

theorem hadamard_diagonal_eq_diagonal_iff {A : Matrix n n α} {d e} :
    A ⊙ diagonal d = diagonal e ↔ A.diag * d = e := by
  simp [hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

end Diagonal

section One

variable [DecidableEq n] [MulZeroOneClass α]
variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ 1 = diagonal M.diag := mul_one M.diag ▸ hadamard_diagonal M 1

theorem one_hadamard : 1 ⊙ M = diagonal M.diag := one_mul M.diag ▸ diagonal_hadamard M 1

theorem one_hadamard_eq_diagonal_iff {A : Matrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d := by
  simpa using diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)

theorem hadamard_one_eq_diagonal_iff {A : Matrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d := by
  simpa using hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)

theorem one_hadamard_eq_zero_iff {A : Matrix n n α} : 1 ⊙ A = 0 ↔ A.diag = 0 := by
  simpa using one_hadamard_eq_diagonal_iff (A := A) (d := 0)

theorem hadamard_one_eq_zero_iff {A : Matrix n n α} : A ⊙ 1 = 0 ↔ A.diag = 0 := by
  simpa using hadamard_one_eq_diagonal_iff (A := A) (d := 0)

theorem one_hadamard_eq_one_iff {A : Matrix n n α} : 1 ⊙ A = 1 ↔ A.diag = 1 :=
  one_hadamard_eq_diagonal_iff

theorem hadamard_one_eq_one_iff {A : Matrix n n α} : A ⊙ 1 = 1 ↔ A.diag = 1 :=
  hadamard_one_eq_diagonal_iff

end One

@[simp] theorem hadamard_of_one [MulOneClass α] (A : Matrix m n α) :
    A ⊙ of 1 = A := by ext; simp

@[simp] theorem of_one_hadamard [MulOneClass α] (A : Matrix m n α) :
    of 1 ⊙ A = A := by ext; simp

theorem hadamard_self_eq_self_iff [Mul α] {A : Matrix m n α} :
    A ⊙ A = A ↔ ∀ i j, IsIdempotentElem (A i j) := ext_iff.symm

section single

variable [DecidableEq m] [DecidableEq n] [MulZeroClass α]

theorem single_hadamard_single_eq (i : m) (j : n) (a b : α) :
    single i j a ⊙ single i j b = single i j (a * b) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

theorem single_hadamard_single_of_ne
    {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia = ib ∧ ja = jb)) (a b : α) :
    single ia ja a ⊙ single ib jb b = 0 := by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

end single

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
