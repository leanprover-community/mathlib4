/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hermitian matrices over ℝ and ℂ

This file proves that Hermitian matrices over ℝ and ℂ are exactly the ones whose corresponding
linear map is self-adjoint.

## Tags

self-adjoint matrix, hermitian matrix
-/
set_option backward.defeqAttrib.useBackward true

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
  simpa using (LinearMap.ext fun x ↦ ext_inner_right _ (h x)).symm

/-- A matrix is Hermitian iff the corresponding linear map on the Euclidean space is
symmetric. -/
@[simp]
lemma isSymmetric_toEuclideanLin_iff [Fintype n] [DecidableEq n] :
    A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian :=
  isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

@[deprecated isSymmetric_toEuclideanLin_iff "use isSymmetric_toEuclideanLin_iff.symm"
  (since := "2026-03-30")]
lemma isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.symm

lemma IsHermitian.im_star_dotProduct_mulVec_self [Fintype n] (hA : A.IsHermitian) (x : n → 𝕜) :
     RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0 := by
  classical
  simpa [dotProduct_comm] using (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

end Matrix

/-- A linear map is symmetric iff the corresponding matrix with an orthonormal basis is
Hermitian. -/
@[simp]
lemma LinearMap.isHermitian_toMatrix_iff {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E →ₗ[𝕜] E} (b : OrthonormalBasis n 𝕜 E) :
    (f.toMatrix b.toBasis b.toBasis).IsHermitian ↔ f.IsSymmetric := by
  rw [← Matrix.isSymmetric_toLin_iff b, Matrix.toLin_toMatrix]
