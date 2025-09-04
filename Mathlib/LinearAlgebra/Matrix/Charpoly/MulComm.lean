/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# AB and BA have the same characteristic polynomial

## References
* https://math.stackexchange.com/a/311362/315369
-/

open Polynomial
open scoped Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]
variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN : M * N = fromBlocks
      (-scalar m X + (A * B).map C) (-(X : R[X]) • A.map C) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar m X) (-A.map C)
      0 ((B * A).map C - scalar n X) := by
    simp [M, N, fromBlocks_multiply, -diagonal_neg, -scalar_apply,
      sub_eq_add_neg, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card n * (scalar m X - (A * B).map C).det) := calc
    _ = (-(scalar m X - (A * B).map C)).det * ((-1) ^ Fintype.card n * X ^ Fintype.card n) := by
      simp [hMN, -diagonal_neg, det_neg, neg_add_eq_sub]
    _ = _ := by simp [-neg_sub, det_neg]; ring
  have hdet_NM : (N * M).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card m * (scalar n X - (B * A).map C).det) := calc
    _ = (-1) ^ Fintype.card m * X ^ Fintype.card m * (-(scalar n X - (B * A).map C)).det := by
      simp [hNM, -diagonal_neg, det_neg]
    _ = _ := by simp [-neg_sub, det_neg]; ring
  simp only [charpoly, charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff, ← hdet_MN, ← hdet_NM, det_mul_comm]

theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
  (isRegular_X_pow _).left.eq_iff.mp <| charpoly_mul_comm' A B

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly :=
  charpoly_units_conj M⁻¹ N

end Matrix
