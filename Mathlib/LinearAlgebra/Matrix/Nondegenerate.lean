/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/


namespace Matrix

variable {m R A : Type*} [CommRing R]

/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w * M * v ≠ 0`. -/
def Nondegenerate [Finite m] (M : Matrix m m R) :=
  letI : Fintype m := Fintype.ofFinite m
  ∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0

variable [Fintype m]

lemma nondegenerate_def {M : Matrix m m R} :
    M.Nondegenerate ↔ ∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0 := by
  refine forall_congr' fun v ↦ ⟨fun hM hv ↦ hM ?_, fun hM hv ↦ hM ?_⟩ <;> convert hv

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, v ⬝ᵥ M *ᵥ w = 0) : v = 0 :=
  nondegenerate_def.mp hM v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero {M : Matrix m m R} (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

variable [CommRing A] [IsDomain A]

/-- If `M` has a nonzero determinant, then `M` as a bilinear form on `n → A` is nondegenerate.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDetNeZero`.
-/
theorem nondegenerate_of_det_ne_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) :
    Nondegenerate M := by
  refine nondegenerate_def.mpr fun v hv ↦ ?_
  ext i
  specialize hv (M.cramer (Pi.single i 1))
  simp_all

theorem eq_zero_of_vecMul_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : v ᵥ* M = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho fun w => by
    rw [dotProduct_mulVec, hv, zero_dotProduct]

theorem eq_zero_of_mulVec_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M *ᵥ v = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)

end Matrix
