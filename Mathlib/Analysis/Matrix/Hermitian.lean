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

/-- A matrix is Hermitian iff the corresponding linear map is self adjoint. -/
lemma isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric := by
  rw [LinearMap.IsSymmetric, (WithLp.toLp_surjective _).forall₂]
  simp only [toLpLin_toLp, Matrix.toLin'_apply, EuclideanSpace.inner_eq_star_dotProduct,
    star_mulVec]
  constructor
  · rintro (h : Aᴴ = A) x y
    rw [dotProduct_comm, ← dotProduct_mulVec, h, dotProduct_comm]
  · intro h
    ext i j
    simpa [(Pi.single_star i 1).symm] using h (Pi.single i 1) (Pi.single j 1)

/-- A version of `Matrix.isHermitian_iff_isSymmetric` that allows using any `OrthonormalBasis`. -/
lemma isHermitian_iff_isSymmetric_of_orthonormalBasis [Fintype n] [DecidableEq n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis n 𝕜 E) :
    IsHermitian A ↔ (A.toLin b.toBasis b.toBasis).IsSymmetric := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  constructor
  · intro (h : Aᴴ = A) x y
    rw [h]
  · intro h
    simpa using (LinearMap.ext fun x ↦ ext_inner_right _ (h x)).symm

lemma IsHermitian.im_star_dotProduct_mulVec_self [Fintype n] (hA : A.IsHermitian) (x : n → 𝕜) :
     RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0 := by
  classical
  simpa [dotProduct_comm] using (isHermitian_iff_isSymmetric.mp hA).im_inner_self_apply _

end Matrix
