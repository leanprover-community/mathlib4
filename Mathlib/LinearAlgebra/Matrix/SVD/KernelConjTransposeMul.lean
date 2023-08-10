/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! # Kernel of the products of a Matrix Conjugate Transpose of a Matrix -/
open Matrix BigOperators

namespace Matrix
variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]
variable {m n p : Type}
variable [Fintype m][DecidableEq m][Fintype n]
variable [DecidableEq n][Fintype l][DecidableEq l]

lemma conjTranspose_mul_self_eq_zero_iff (A: Matrix m n 𝕂):
    (Aᴴ⬝A) = 0 ↔ A = 0 := by
  refine' ⟨ fun h => _, fun h => by simp only [h, Matrix.mul_zero] ⟩
  funext i j
  rw [← Matrix.ext_iff] at h
  specialize h j j
  rw [IsROrC.ext_iff] at h
  simp only [mul_apply, Matrix.zero_apply, map_zero, conjTranspose_apply, IsROrC.star_def,
    IsROrC.conj_mul, map_sum, IsROrC.ofReal_im, Finset.sum_const_zero, and_true, IsROrC.ofReal_re] at h
  apply IsROrC.normSq_eq_zero.1
  apply (Finset.sum_eq_zero_iff_of_nonneg (?_)).1 h
  exact Finset.mem_univ _
  exact (fun _ => (fun _ => IsROrC.normSq_nonneg _))


lemma ker_conj_transpose_mul_self_eq_ker (A: Matrix m n 𝕂)(B: Matrix n p 𝕂) :
    (Aᴴ⬝A)⬝B = 0 ↔ A⬝B = 0 := by
  constructor
  intros h
  apply_fun (fun x => Bᴴ.mul x) at h
  rw [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul] at h
  exact (conjTranspose_mul_self_eq_zero_iff (A⬝B)).1 h
  intros h
  rw [Matrix.mul_assoc, h, Matrix.mul_zero]

lemma ker_self_mul_conj_transpose_eq_ker_conj_transpose (A: Matrix m n 𝕂)(B: Matrix m p 𝕂) :
    (A⬝Aᴴ)⬝B = 0 ↔ Aᴴ⬝B = 0 := by
  simpa only [conjTranspose_conjTranspose] using ker_conj_transpose_mul_self_eq_ker Aᴴ _

end Matrix
