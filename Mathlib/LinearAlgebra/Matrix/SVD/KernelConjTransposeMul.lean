/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SVD.IsROrCStarOrderedRing

/-! # Kernel of the products of a Matrix Conjugate Transpose of a Matrix -/
open Matrix BigOperators

namespace Matrix
variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]
variable {m n p : Type}
variable [Fintype m][DecidableEq m][Fintype n]
variable [DecidableEq n][Fintype l][DecidableEq l]

lemma conjTranspose_mul_self_eq_zero_iff (A: Matrix m n 𝕂):
  (Aᴴ⬝A) = 0 ↔ A = 0 := by
  constructor
  · intros h
    funext i j
    rw [← Matrix.ext_iff] at h
    specialize h j j
    simp_rw [mul_apply, Matrix.zero_apply, conjTranspose_apply, IsROrC.star_def,
      IsROrC.conj_mul] at h
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h
    specialize h i
    simp only [Finset.mem_univ, algebraMap.lift_map_eq_zero_iff, map_eq_zero, forall_true_left] at h
    rwa [Matrix.zero_apply]
    simp only [Finset.mem_univ, forall_true_left]
    intros x
    rw [IsROrC.le_def]
    simp only [map_zero, IsROrC.ofReal_re, IsROrC.ofReal_im, and_true]
    apply IsROrC.normSq_nonneg
  · intros h
    rw [h]
    simp only [Matrix.mul_zero]

lemma ker_conj_transpose_mul_self_eq_ker (A: Matrix m n 𝕂)(B: Matrix n p 𝕂) :
  (Aᴴ⬝A)⬝B = 0 ↔ A⬝B = 0 := by
  constructor
  intros h
  apply_fun (fun x => Bᴴ.mul x) at h
  rw [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← conjTranspose_mul] at h
  exact (conjTranspose_mul_self_eq_zero_iff (A⬝B)).1 h
  intros h
  rw [Matrix.mul_assoc, h, Matrix.mul_zero]

lemma ker_self_mul_conj_transpose_eq_ker_conj_transpose (A: Matrix m n 𝕂)(B: Matrix m p 𝕂) :
  (A⬝Aᴴ)⬝B = 0 ↔ Aᴴ⬝B = 0 := by
  constructor
  intros h
  apply_fun (fun x => Bᴴ.mul x) at h
  have hbha: Bᴴ ⬝ A = (Aᴴ⬝B)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, hbha] at h
  exact (conjTranspose_mul_self_eq_zero_iff (Aᴴ⬝B)).1 h
  intros h
  rw [Matrix.mul_assoc, h, Matrix.mul_zero]

end Matrix
