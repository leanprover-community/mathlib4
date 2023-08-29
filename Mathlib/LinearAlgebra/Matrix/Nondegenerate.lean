/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Adjugate

#align_import linear_algebra.matrix.nondegenerate from "leanprover-community/mathlib"@"2a32c70c78096758af93e997b978a5d461007b4f"

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/


namespace Matrix

variable {m R A : Type*} [Fintype m] [CommRing R]

/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w * M * v ≠ 0`. -/
def Nondegenerate (M : Matrix m m R) :=
  ∀ v, (∀ w, Matrix.dotProduct v (mulVec M w) = 0) → v = 0
#align matrix.nondegenerate Matrix.Nondegenerate

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, Matrix.dotProduct v (mulVec M w) = 0) : v = 0 :=
  hM v hv
#align matrix.nondegenerate.eq_zero_of_ortho Matrix.Nondegenerate.eq_zero_of_ortho

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero {M : Matrix m m R} (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, Matrix.dotProduct v (mulVec M w) ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)
#align matrix.nondegenerate.exists_not_ortho_of_ne_zero Matrix.Nondegenerate.exists_not_ortho_of_ne_zero

variable [CommRing A] [IsDomain A]

/-- If `M` has a nonzero determinant, then `M` as a bilinear form on `n → A` is nondegenerate.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDetNeZero`.
-/
theorem nondegenerate_of_det_ne_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) :
    Nondegenerate M := by
  intro v hv
  -- ⊢ v = 0
  ext i
  -- ⊢ v i = OfNat.ofNat 0 i
  specialize hv (M.cramer (Pi.single i 1))
  -- ⊢ v i = OfNat.ofNat 0 i
  refine' (mul_eq_zero.mp _).resolve_right hM
  -- ⊢ v i * det M = 0
  convert hv
  -- ⊢ v i * det M = v ⬝ᵥ mulVec M (↑(cramer M) (Pi.single i 1))
  simp only [mulVec_cramer M (Pi.single i 1), dotProduct, Pi.smul_apply, smul_eq_mul]
  -- ⊢ v i * det M = Finset.sum Finset.univ fun x => v x * (det M * Pi.single i 1 x)
  rw [Finset.sum_eq_single i, Pi.single_eq_same, mul_one]
  -- ⊢ ∀ (b : m), b ∈ Finset.univ → b ≠ i → v b * (det M * Pi.single i 1 b) = 0
  · intro j _ hj
    -- ⊢ v j * (det M * Pi.single i 1 j) = 0
    simp [hj]
    -- 🎉 no goals
  · intros
    -- ⊢ v i * (det M * Pi.single i 1 i) = 0
    have := Finset.mem_univ i
    -- ⊢ v i * (det M * Pi.single i 1 i) = 0
    contradiction
    -- 🎉 no goals
#align matrix.nondegenerate_of_det_ne_zero Matrix.nondegenerate_of_det_ne_zero

theorem eq_zero_of_vecMul_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M.vecMul v = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho fun w => by
    rw [dotProduct_mulVec, hv, zero_dotProduct]
    -- 🎉 no goals
#align matrix.eq_zero_of_vec_mul_eq_zero Matrix.eq_zero_of_vecMul_eq_zero

theorem eq_zero_of_mulVec_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M.mulVec v = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)
                                -- 🎉 no goals
#align matrix.eq_zero_of_mul_vec_eq_zero Matrix.eq_zero_of_mulVec_eq_zero

end Matrix
