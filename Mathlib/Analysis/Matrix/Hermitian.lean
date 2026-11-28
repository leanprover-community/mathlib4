/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Hermitian matrices over ℝ and ℂ

This file proves that Hermitian matrices over ℝ and ℂ are exactly the ones whose corresponding
linear map is self-adjoint.

## Tags

self-adjoint matrix, hermitian matrix
-/

public section

-- TODO:
-- assert_not_exists MonoidAlgebra

open RCLike

namespace Matrix

variable {𝕜 m n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜]

/-- The diagonal elements of a complex Hermitian matrix are real. -/
lemma IsHermitian.coe_re_apply_self (h : A.IsHermitian) (i : n) : (re (A i i) : 𝕜) = A i i := by
  rw [← conj_eq_iff_re, ← star_def, ← conjTranspose_apply, h.eq]

/-- The diagonal elements of a complex Hermitian matrix are real. -/
lemma IsHermitian.coe_re_diag (h : A.IsHermitian) : (fun i => (re (A.diag i) : 𝕜)) = A.diag :=
  funext h.coe_re_apply_self

/-- A matrix is Hermitian iff the corresponding linear map with an orthonormal basis is
symmetric. -/
@[simp]
lemma isSymmetric_toLin_iff [Fintype n] [DecidableEq n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis n 𝕜 E) :
    (A.toLin b.toBasis b.toBasis).IsSymmetric ↔ A.IsHermitian := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ by rw [h.eq]⟩
  simpa using! (LinearMap.ext fun x ↦ ext_inner_right _ (h x)).symm

/-- A matrix is Hermitian iff the corresponding linear map on the Euclidean space is
symmetric. -/
@[simp]
lemma isSymmetric_toEuclideanLin_iff [Fintype n] [DecidableEq n] :
    A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian :=
  isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

lemma ext_iff_finsuppSum_star_mul_mul_complex {A B : Matrix n n ℂ} :
    A = B ↔ ∀ x : n →₀ ℂ,
      (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj) =
        x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * B i j * xj := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ext fun i j ↦ ?_⟩
  have hAB (i : n) : A i i = B i i := by simpa using h (.single i 1)
  have h2 := h (.single i 1 + .single j 1)
  have h3 := h (.single i 1 + .single j .I)
  simp_all [Finsupp.sum_add_index', add_mul, mul_add, Complex.ext_iff]
  grind

lemma ext_iff_dotProduct_mulVec_complex [Fintype n] {A B : Matrix n n ℂ} :
    A = B ↔ ∀ x : n → ℂ, star x ⬝ᵥ A *ᵥ x = star x ⬝ᵥ B *ᵥ x := by
  rw [ext_iff_finsuppSum_star_mul_mul_complex]
  simp [Finsupp.sum_fintype, dotProduct, mulVec, Finset.mul_sum,
    ← Finsupp.equivFunOnFinite.forall_congr_right, mul_assoc]

lemma isHermitian_iff_complex {A : Matrix n n ℂ} :
    A.IsHermitian ↔
      ∀ x : n →₀ ℂ, (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj).im = 0 := by
  simp_rw [← Complex.conj_eq_iff_im, ← Complex.star_def, star_finsuppSum, Pi.star_apply,
    star_finsuppSum, Pi.star_apply, star_mul, star_star, IsHermitian,
    ext_iff_finsuppSum_star_mul_mul_complex, conjTranspose_apply, mul_assoc]
  apply forall_congr' fun x ↦ ?_
  rw [Finsupp.sum_comm]

lemma isHermitian_iff_im_dotProduct_mulVec_eq_zero_complex [Fintype n] {A : Matrix n n ℂ} :
    A.IsHermitian ↔ ∀ x : n → ℂ, (star x ⬝ᵥ A *ᵥ x).im = 0 := by
  simp [isHermitian_iff_complex, ← Finsupp.equivFunOnFinite.forall_congr_right,
    Finsupp.sum_fintype, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma IsHermitian.im_star_dotProduct_mulVec_self [Fintype n] (hA : A.IsHermitian) (x : n → 𝕜) :
     RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0 := by
  classical
  simpa [dotProduct_comm] using! (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

end Matrix

/-- A linear map is symmetric iff the corresponding matrix with an orthonormal basis is
Hermitian. -/
@[simp]
lemma LinearMap.isHermitian_toMatrix_iff {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E →ₗ[𝕜] E} (b : OrthonormalBasis n 𝕜 E) :
    (f.toMatrix b.toBasis b.toBasis).IsHermitian ↔ f.IsSymmetric := by
  rw [← Matrix.isSymmetric_toLin_iff b, Matrix.toLin_toMatrix]
