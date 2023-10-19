/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Elementary Matrix
-/

namespace Matrix

universe u v

open Matrix

variable {n : Type u} [DecidableEq n] {R : Type v}

/-- A matrix with only one nonzero element.-/
def Single [AddMonoid R] (i j : n) (c : R) : Matrix n n R := of fun (k1 : n) (k2 : n) =>
  if k1 = i ∧ k2 = j then c
  else 0

/-- A matrix of elementary row/column operation.
Multiplying this matrix on the left is equivalent to
adding `c` times the j-th row to the i-th row.
Multiplying this matrix on the right is equivalent to
adding `c` times the i-th column to the j-th column.
-/
def Elementary [AddMonoidWithOne R] (i j : n) (c : R) : Matrix n n R := 1 + Single i j c

variable [CommRing R]

section BlockTriangular

variable {α : Type*} (b : n → α)

theorem blockTriangular_id  [Preorder α] : BlockTriangular (1 : Matrix n n R) b := by
  rw [← @diagonal_one]
  exact blockTriangular_diagonal fun _ ↦ 1

theorem blockTriangular_Single [LinearOrder α] (i j : n) (c : R) :
    BlockTriangular (Single i j c) b ∨
    BlockTriangular (Single i j c) (OrderDual.toDual ∘ b) := by
  by_cases hij : b i = b j
  · left
    unfold BlockTriangular Single
    aesop
  · by_cases h : b i < b j
    · left
      intro r s hrs
      unfold Single
      simp only [of_apply, ite_eq_right_iff, and_imp]
      intro hr hs
      rw [hr, hs] at hrs
      exact h.trans hrs |>.false.elim
    · right
      push_neg at hij
      push_neg at h
      replace h := hij.symm.lt_of_le h
      replace h : (OrderDual.toDual ∘ b) i < (OrderDual.toDual ∘ b) j := h
      intro r s hrs
      unfold Single
      simp only [of_apply, ite_eq_right_iff, and_imp]
      intro hr hs
      rw [hr, hs] at hrs
      exact h.trans hrs |>.false.elim

theorem blockTriangular_Elementary [LinearOrder α] (i j : n) (c : R) :
    BlockTriangular (Elementary i j c) b ∨
    BlockTriangular (Elementary i j c) (OrderDual.toDual ∘ b) :=
  (blockTriangular_Single b i j c).imp
    (BlockTriangular.add <| blockTriangular_id b)
    (BlockTriangular.add <| blockTriangular_id <| OrderDual.toDual ∘ b)

end BlockTriangular
