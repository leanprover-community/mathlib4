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

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly := by
  let M := fromBlocks (scalar n X) (C.mapMatrix A) (C.mapMatrix B) 1
  let N := fromBlocks (-1 : Matrix n n R[X]) 0 (C.mapMatrix B) (-scalar n X)
  have hMN : M * N = fromBlocks
      (-scalar n X + C.mapMatrix (A * B)) (-(X : R[X]) • C.mapMatrix A) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar n X) (-C.mapMatrix A)
      0 (C.mapMatrix (B * A) - scalar n X) := by
    simp [M, N, fromBlocks_multiply, -diagonal_neg, -scalar_apply, sub_eq_add_neg, scalar_comm]
  have hdet_MN : (M * N).det = X ^ Fintype.card n * (scalar n X - C.mapMatrix (A * B)).det := calc
    _ = (-scalar n X + C.mapMatrix (A * B)).det * (-1 : Matrix n n R[X]).det *
        X ^ Fintype.card n := by
      simp [hMN, det_neg]
      ring
    _ = _ := by simp [← det_mul, neg_add_eq_sub]; ring
  have hdet_NM : (N * M).det = X ^ Fintype.card n * (scalar n X - C.mapMatrix (B * A)).det := calc
    _ = X ^ Fintype.card n *
        ((-1 : Matrix n n R[X]).det * (C.mapMatrix (B * A) - scalar n X).det) := by
      simp [hNM, det_neg]
      ring
    _ = _ := by simp [← det_mul]
  unfold charpoly charmatrix
  rw [← X_pow_mul_inj, ← hdet_MN, ← hdet_NM, det_mul_comm]

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly :=
  charpoly_units_conj M⁻¹ N

end Matrix
