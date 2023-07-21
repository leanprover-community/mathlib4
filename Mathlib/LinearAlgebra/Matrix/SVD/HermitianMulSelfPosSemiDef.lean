/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.SVD.IsROrCStarOrderedRing
import Mathlib.LinearAlgebra.Matrix.SVD.RankMulIsUnit
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # AᴴA is Positive Semidefinite with Non-negative eigenvalues -/

variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]

open Matrix BigOperators

lemma conj_transpose_mul_self_is_pos_semidef {m n: Type}
  [Fintype m][Fintype n]
  (A: Matrix m n 𝕂): Matrix.PosSemidef (Aᴴ⬝A) := by
  constructor
  exact (isHermitian_transpose_mul_self A)
  intro v
  rw [←mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
  rw [star_star]
  set z := mulVec A v
  have : 0 ≤ star z ⬝ᵥ z := by
    rw [dotProduct]
    apply Finset.sum_nonneg
    intros i _
    apply star_mul_self_nonneg
  rw [IsROrC.le_def, map_zero] at this
  exact this.1

lemma eigenvalues_nonneg_of_pos_semidef {n: Type}
  [Fintype n][DecidableEq n] (A: Matrix n n 𝕂)(hA: Matrix.PosSemidef A)(i: n):
  0 ≤ hA.1.eigenvalues i := by
  rw [hA.1.eigenvalues_eq]
  apply hA.2

lemma sing_vals_ne_zero_pos {m n: Type}
  [Fintype m][Fintype n][DecidableEq n]
  (A: Matrix m n 𝕂)
  (z: {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0 }):
    0 < Real.sqrt ((isHermitian_transpose_mul_self A).eigenvalues z) := by
  rw [Real.sqrt_pos]
  apply lt_of_le_of_ne
  apply eigenvalues_nonneg_of_pos_semidef
  exact (conj_transpose_mul_self_is_pos_semidef A)
  exact z.prop.symm

lemma eig_vals_ne_zero_pos {m n: Type}
  [Fintype m][Fintype n][DecidableEq n]
  (A: Matrix m n 𝕂)
  (z: {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0 }):
    0 < ((isHermitian_transpose_mul_self A).eigenvalues z) := by
  apply lt_of_le_of_ne
  apply eigenvalues_nonneg_of_pos_semidef
  exact (conj_transpose_mul_self_is_pos_semidef A)
  exact z.prop.symm
