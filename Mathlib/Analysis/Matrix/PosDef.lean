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

open WithLp
open scoped ComplexOrder

namespace Matrix
variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]

/-! ### Positive semidefinite matrices -/

namespace PosSemidef

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  (hA.re_dotProduct_nonneg _).trans_eq (hA.1.eigenvalues_eq _).symm

lemma det_nonneg [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    0 ≤ M.det := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ ↦ by simpa using hM.eigenvalues_nonneg i

end PosSemidef

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : IsHermitian A) : PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  refine ⟨fun h => h.eigenvalues_nonneg, fun h => ?_⟩
  rw [hA.spectral_theorem]
  refine (posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  simpa using h

@[deprecated (since := "2025-08-17")] alias ⟨_, IsHermitian.posSemidef_of_eigenvalues_nonneg⟩ :=
  IsHermitian.posSemidef_iff_eigenvalues_nonneg

lemma PosSemidef.trace_eq_zero_iff {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.trace = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ trace_zero n 𝕜⟩
  classical
  simp_rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum,
    RCLike.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (by simpa using hA.eigenvalues_nonneg), Finset.mem_univ, true_imp_iff] at h
  exact funext_iff.eq ▸ hA.isHermitian.eigenvalues_eq_zero_iff.mp <| h

/-! ### Positive definite matrices -/

namespace PosDef

/-- The eigenvalues of a positive definite matrix are positive. -/
lemma eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i := by
  simp only [hA.1.eigenvalues_eq]
  exact hA.re_dotProduct_pos <| (ofLp_eq_zero 2).ne.2 <|
    hA.1.eigenvectorBasis.orthonormal.ne_zero i

/-- A Hermitian matrix is positive-definite if and only if its eigenvalues are positive. -/
lemma _root_.Matrix.IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := by
  refine ⟨fun h => h.eigenvalues_pos, fun h => ?_⟩
  rw [hA.spectral_theorem]
  refine (posDef_diagonal_iff.mpr <| by simpa using h).mul_mul_conjTranspose_same ?_
  rw [vecMul_injective_iff_isUnit, ← Unitary.val_toUnits_apply]
  exact Units.isUnit _

lemma det_pos [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hM.eigenvalues_pos i

end PosDef
end Matrix
