/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spectrum of positive definite matrices

This file proves that eigenvalues of positive (semi)definite matrices are (nonnegative) positive.
-/

open WithLp Matrix Unitary
open scoped ComplexOrder

namespace Matrix
variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]

/-! ### Positive semidefinite matrices -/

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : IsHermitian A) : PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

@[deprecated (since := "2025-08-17")] alias ⟨_, IsHermitian.posSemidef_of_eigenvalues_nonneg⟩ :=
  IsHermitian.posSemidef_iff_eigenvalues_nonneg

namespace PosSemidef

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _

lemma det_nonneg [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    0 ≤ M.det := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ ↦ by simpa using hM.eigenvalues_nonneg i

lemma trace_eq_zero_iff {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.trace = 0 ↔ A = 0 := by
  classical
  conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self,
    one_mul, trace_diagonal, Finset.sum_eq_zero_iff_of_nonneg (by simp [hA.eigenvalues_nonneg])]
  simp [← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff]

end PosSemidef

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-! ### Positive definite matrices -/

/-- A Hermitian matrix is positive-definite if and only if its eigenvalues are positive. -/
lemma IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

namespace PosDef

/-- The eigenvalues of a positive definite matrix are positive. -/
lemma eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i :=
  hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i

lemma det_pos [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hM.eigenvalues_pos i

end PosDef
end Matrix
