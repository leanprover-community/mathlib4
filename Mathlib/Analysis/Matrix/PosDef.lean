/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spectrum of positive (semi)definite matrices

This file proves that eigenvalues of positive (semi)definite matrices are (nonnegative) positive.

## Main definitions

* `Matrix.toInnerProductSpace`: the pre-inner product space on `n → 𝕜` induced by a
  positive semi-definite matrix `M`, and is given by `⟪x, y⟫ = xᴴMy`.

-/

@[expose] public section

open WithLp Matrix Unitary
open scoped ComplexOrder

namespace Matrix
variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜] {A : Matrix n n 𝕜}

/-! ### Positive semidefinite matrices -/

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] (hA : IsHermitian A) :
    PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

@[deprecated (since := "2025-08-17")] alias ⟨_, IsHermitian.posSemidef_of_eigenvalues_nonneg⟩ :=
  IsHermitian.posSemidef_iff_eigenvalues_nonneg

namespace PosSemidef

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] (hA : A.PosSemidef) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _

lemma re_dotProduct_nonneg (hA : A.PosSemidef) (x : n → 𝕜) : 0 ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x)) :=
  RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _) |>.1

lemma det_nonneg [DecidableEq n] (hA : A.PosSemidef) : 0 ≤ A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ ↦ by simpa using hA.eigenvalues_nonneg i

lemma trace_eq_zero_iff (hA : A.PosSemidef) : A.trace = 0 ↔ A = 0 := by
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
lemma IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

namespace PosDef

lemma re_dotProduct_pos (hA : A.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx) |>.1

/-- The eigenvalues of a positive definite matrix are positive. -/
lemma eigenvalues_pos [DecidableEq n] (hA : A.PosDef) (i : n) : 0 < hA.1.eigenvalues i :=
  hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i

lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hA.eigenvalues_pos i

end PosDef

/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toSeminormedAddCommGroup`, `Matrix.toNormedAddCommGroup`,
and `Matrix.toInnerProductSpace`. -/
private def PosSemidef.preInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (n → 𝕜) where
  inner x y := (M *ᵥ y) ⬝ᵥ star x
  conj_inner_symm x y := by
    rw [dotProduct_comm, star_dotProduct, starRingEnd_apply, star_star,
      star_mulVec, dotProduct_comm (M *ᵥ y), dotProduct_mulVec, hM.isHermitian.eq]
  re_inner_nonneg x := dotProduct_comm _ (star x) ▸ hM.re_dotProduct_nonneg x
  add_left := by simp only [star_add, dotProduct_add, forall_const]
  smul_left _ _ _ := by rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul]

/-- A positive semi-definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
noncomputable abbrev toSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.preInnerProductSpace

/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
noncomputable abbrev toNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
  { __ := hM.posSemidef.preInnerProductSpace
    definite x (hx : _ ⬝ᵥ _ = 0) := by
      by_contra! h
      simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h }

/-- A positive semi-definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def toInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM) :=
  InnerProductSpace.ofCore _

@[deprecated (since := "2025-10-26")] alias NormedAddCommGroup.ofMatrix := toNormedAddCommGroup
@[deprecated (since := "2025-10-26")] alias InnerProductSpace.ofMatrix := toInnerProductSpace

end Matrix
