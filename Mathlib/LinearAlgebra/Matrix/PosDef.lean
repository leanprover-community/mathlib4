/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basic

#align_import linear_algebra.matrix.pos_def from "leanprover-community/mathlib"@"07992a1d1f7a4176c6d3f160209608be4e198566"

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.

## Main definition

* `Matrix.PosDef` : a matrix `M : Matrix n n 𝕜` is positive definite if it is hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.
* `Matrix.PosSemidef` : a matrix `M : Matrix n n 𝕜` is positive semidefinite if it is hermitian
  and `xᴴMx` is nonnegative for all `x`.

-/

open scoped ComplexOrder


namespace Matrix

variable {m n R 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [CommRing R] [PartialOrder R] [StarOrderedRing R]
variable [IsROrC 𝕜]
open scoped Matrix

/-- A matrix `M : Matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M.mulVec x)
#align matrix.pos_def Matrix.PosDef

theorem PosDef.isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
#align matrix.pos_def.is_hermitian Matrix.PosDef.isHermitian

theorem PosDef.re_dotProduct_pos {M : Matrix n n 𝕜} (hM : M.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < IsROrC.re (dotProduct (star x) (M.mulVec x)) :=
  IsROrC.pos_iff.mp (hM.2 _ hx) |>.1

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M.mulVec x)
#align matrix.pos_semidef Matrix.PosSemidef

theorem PosSemidef.re_dotProduct_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (x : n → 𝕜) :
    0 ≤ IsROrC.re (dotProduct (star x) (M.mulVec x)) :=
  IsROrC.nonneg_iff.mp (hM.2 _) |>.1

theorem PosDef.posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef := by
  refine' ⟨hM.1, _⟩
  -- ⊢ ∀ (x : n → R), 0 ≤ star x ⬝ᵥ mulVec M x
  intro x
  -- ⊢ 0 ≤ star x ⬝ᵥ mulVec M x
  by_cases hx : x = 0
  -- ⊢ 0 ≤ star x ⬝ᵥ mulVec M x
  · simp only [hx, zero_dotProduct, star_zero, IsROrC.zero_re']
    -- ⊢ 0 ≤ 0
    exact le_rfl
    -- 🎉 no goals
  · exact le_of_lt (hM.2 x hx)
    -- 🎉 no goals
#align matrix.pos_def.pos_semidef Matrix.PosDef.posSemidef

theorem PosSemidef.submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m ≃ n) :
    (M.submatrix e e).PosSemidef := by
  refine' ⟨hM.1.submatrix e, fun x => _⟩
  -- ⊢ 0 ≤ star x ⬝ᵥ mulVec (Matrix.submatrix M ↑e ↑e) x
  have : (M.submatrix (⇑e) e).mulVec x = (M.mulVec fun i : n => x (e.symm i)) ∘ e := by
    ext i
    dsimp only [(· ∘ ·), mulVec, dotProduct]
    rw [Finset.sum_bij' (fun i _ => e i) _ _ fun i _ => e.symm i] <;>
      simp only [eq_self_iff_true, imp_true_iff, Equiv.symm_apply_apply, Finset.mem_univ,
        submatrix_apply, Equiv.apply_symm_apply]
  rw [this]
  -- ⊢ 0 ≤ star x ⬝ᵥ (mulVec M fun i => x (↑e.symm i)) ∘ ↑e
  convert hM.2 fun i => x (e.symm i) using 3
  -- ⊢ star x ⬝ᵥ (mulVec M fun i => x (↑e.symm i)) ∘ ↑e = (star fun i => x (↑e.symm …
  unfold dotProduct
  -- ⊢ (Finset.sum Finset.univ fun i => star x i * ((mulVec M fun i => x (↑e.symm i …
  rw [Finset.sum_bij' (fun i _ => e i) _ _ fun i _ => e.symm i] <;>
  simp
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align matrix.pos_semidef.submatrix Matrix.PosSemidef.submatrix

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
               -- 🎉 no goals
#align matrix.pos_semidef_submatrix_equiv Matrix.posSemidef_submatrix_equiv

theorem PosDef.transpose {M : Matrix n n R} (hM : M.PosDef) : Mᵀ.PosDef := by
  refine ⟨IsHermitian.transpose hM.1, fun x hx => ?_⟩
  -- ⊢ 0 < star x ⬝ᵥ mulVec Mᵀ x
  convert hM.2 (star x) (star_ne_zero.2 hx) using 1
  -- ⊢ star x ⬝ᵥ mulVec Mᵀ x = star (star x) ⬝ᵥ mulVec M (star x)
  rw [mulVec_transpose, Matrix.dotProduct_mulVec, star_star, dotProduct_comm]
  -- 🎉 no goals
#align matrix.pos_def.transpose Matrix.PosDef.transpose

theorem posDef_of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine' ⟨hM, fun x hx => _⟩
  -- ⊢ 0 < star x ⬝ᵥ mulVec M x
  simp only [toQuadraticForm', QuadraticForm.PosDef, BilinForm.toQuadraticForm_apply,
    Matrix.toBilin'_apply'] at hMq
  apply hMq x hx
  -- 🎉 no goals
#align matrix.pos_def_of_to_quadratic_form' Matrix.posDef_of_toQuadraticForm'

theorem posDef_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  -- ⊢ 0 < ↑(toQuadraticForm' M) x
  simp only [toQuadraticForm', BilinForm.toQuadraticForm_apply, Matrix.toBilin'_apply']
  -- ⊢ 0 < x ⬝ᵥ mulVec M x
  apply hM.2 x hx
  -- 🎉 no goals
#align matrix.pos_def_to_quadratic_form' Matrix.posDef_toQuadraticForm'

/-- The conjugate transpose of a matrix mulitplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self (A : Matrix m n R) : Matrix.PosSemidef (Aᴴ * A) := by
  refine ⟨isHermitian_transpose_mul_self _, fun x => ?_⟩
  -- ⊢ 0 ≤ star x ⬝ᵥ mulVec (Aᴴ * A) x
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  -- ⊢ 0 ≤ star (mulVec A x) ⬝ᵥ mulVec A x
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
  -- 🎉 no goals

/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
theorem posSemidef_self_mul_conjTranspose (A : Matrix m n R) : Matrix.PosSemidef (A * Aᴴ) :=
  by simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ
     -- 🎉 no goals

/-- The eigenvalues of a positive definite matrix are positive -/
lemma PosDef.eigenvalues_pos [DecidableEq n] [DecidableEq 𝕜] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i := by
  rw [hA.1.eigenvalues_eq, hA.1.transpose_eigenvectorMatrix_apply]
  -- ⊢ 0 < ↑IsROrC.re (star (↑(IsHermitian.eigenvectorBasis (_ : IsHermitian A)) i) …
  exact hA.re_dotProduct_pos <| hA.1.eigenvectorBasis.orthonormal.ne_zero i
  -- 🎉 no goals

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma PosSemidef.eigenvalues_nonneg [DecidableEq n] [DecidableEq 𝕜] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  (hA.re_dotProduct_nonneg _).trans_eq (hA.1.eigenvalues_eq _).symm

namespace PosDef

variable {M : Matrix n n ℝ} (hM : M.PosDef)

theorem det_pos [DecidableEq n] : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  -- ⊢ 0 < Finset.prod Finset.univ fun i => ↑(IsHermitian.eigenvalues (_ : IsHermit …
  apply Finset.prod_pos
  -- ⊢ ∀ (i : n), i ∈ Finset.univ → 0 < ↑(IsHermitian.eigenvalues (_ : IsHermitian  …
  intro i _
  -- ⊢ 0 < ↑(IsHermitian.eigenvalues (_ : IsHermitian M) i)
  rw [hM.isHermitian.eigenvalues_eq]
  -- ⊢ 0 < ↑(↑IsROrC.re (star ((IsHermitian.eigenvectorMatrix (_ : IsHermitian M))ᵀ …
  refine hM.2 _ fun h => ?_
  -- ⊢ False
  have h_det : hM.isHermitian.eigenvectorMatrixᵀ.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i fun j => congr_fun h j
  simpa only [h_det, not_isUnit_zero] using
    isUnit_det_of_invertible hM.isHermitian.eigenvectorMatrixᵀ
#align matrix.pos_def.det_pos Matrix.PosDef.det_pos

end PosDef

end Matrix

namespace QuadraticForm

variable {n : Type*} [Fintype n]

theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q, ← BilinForm.toMatrix'.left_inv ((associatedHom ℝ) Q)]
  -- ⊢ PosDef (BilinForm.toQuadraticForm (LinearEquiv.invFun BilinForm.toMatrix' (A …
  apply Matrix.posDef_toQuadraticForm' hQ
  -- 🎉 no goals
#align quadratic_form.pos_def_of_to_matrix' QuadraticForm.posDef_of_toMatrix'

theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q, ←
    BilinForm.toMatrix'.left_inv ((associatedHom ℝ) Q)] at hQ
  apply Matrix.posDef_of_toQuadraticForm' (isSymm_toMatrix' Q) hQ
  -- 🎉 no goals
#align quadratic_form.pos_def_to_matrix' QuadraticForm.posDef_toMatrix'

end QuadraticForm

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]

/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
@[reducible]
noncomputable def NormedAddCommGroup.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
    { inner := fun x y => dotProduct (star x) (M.mulVec y)
      conj_symm := fun x y => by
        dsimp only [Inner.inner]
        -- ⊢ ↑(starRingEnd 𝕜) (star y ⬝ᵥ mulVec M x) = star x ⬝ᵥ mulVec M y
        rw [star_dotProduct, starRingEnd_apply, star_star, star_mulVec, dotProduct_mulVec,
          hM.isHermitian.eq]
      nonneg_re := fun x => by
        by_cases h : x = 0
        -- ⊢ 0 ≤ ↑IsROrC.re (inner x x)
        · simp [h]
          -- 🎉 no goals
        · exact le_of_lt (hM.re_dotProduct_pos h)
          -- 🎉 no goals
      definite := fun x (hx : dotProduct _ _ = 0) => by
        by_contra' h
        -- ⊢ False
        simpa [hx, lt_irrefl] using hM.re_dotProduct_pos h
        -- 🎉 no goals
      add_left := by simp only [star_add, add_dotProduct, eq_self_iff_true, forall_const]
                     -- 🎉 no goals
      smul_left := fun x y r => by
        simp only
        -- ⊢ star (r • x) ⬝ᵥ mulVec M y = ↑(starRingEnd 𝕜) r * star x ⬝ᵥ mulVec M y
        rw [← smul_eq_mul, ← smul_dotProduct, starRingEnd_apply, ← star_smul] }
        -- 🎉 no goals
#align matrix.normed_add_comm_group.of_matrix Matrix.NormedAddCommGroup.ofMatrix

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hM) :=
  InnerProductSpace.ofCore _
#align matrix.inner_product_space.of_matrix Matrix.InnerProductSpace.ofMatrix

end Matrix
