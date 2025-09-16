/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Field.Subfield.Defs

/-!
# Matrices and base change

This file is a home for results about base change for matrices.

## Main results:
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (right) inverse.
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (left) inverse.

-/

namespace Matrix

variable {m n L : Type*} [Finite m] [Fintype n] [DecidableEq m] [Field L]
  (e : m ≃ n) (K : Subfield L) {A : Matrix m n L} {B : Matrix n m L} (hAB : A * B = 1)

include e hAB

lemma mem_subfield_of_mul_eq_one_of_mem_subfield_right
    (h_mem : ∀ i j, A i j ∈ K) (i : n) (j : m) :
    B i j ∈ K := by
  cases nonempty_fintype m
  let A' : Matrix m m K := of fun i j ↦ ⟨A.submatrix id e i j, h_mem i (e j)⟩
  have hA' : A'.map K.subtype = A.submatrix id e := rfl
  have hA : IsUnit A' := by
    have h_unit : IsUnit (A.submatrix id e) :=
      isUnit_of_right_inverse (B := B.submatrix e id) (by simpa)
    have h_det : (A.submatrix id e).det = K.subtype A'.det := by
      simp [A', K.subtype.map_det, map, submatrix]
    simpa [isUnit_iff_isUnit_det, h_det] using h_unit
  obtain ⟨B', hB⟩ := exists_right_inverse_iff_isUnit.mpr hA
  suffices (B'.submatrix e.symm id).map K.subtype = B by simp [← this]
  replace hB : A * (B'.submatrix e.symm id).map K.subtype = 1 := by
    replace hB := congr_arg (fun C ↦ C.map K.subtype) hB
    simp_rw [Matrix.map_mul] at hB
    rw [hA', ← e.symm_symm, ← submatrix_id_mul_left] at hB
    simpa using hB
  classical
  simpa [← Matrix.mul_assoc, (mul_eq_one_comm_of_equiv e).mp hAB] using congr_arg (B * ·) hB

lemma mem_subfield_of_mul_eq_one_of_mem_subfield_left
    (h_mem : ∀ i j, B i j ∈ K) (i : m) (j : n) :
    A i j ∈ K := by
  replace hAB : Bᵀ * Aᵀ = 1 := by simpa using congr_arg transpose hAB
  rw [← A.transpose_apply]
  simp_rw [← B.transpose_apply] at h_mem
  exact mem_subfield_of_mul_eq_one_of_mem_subfield_right e K hAB (fun i j ↦ h_mem j i) j i

end Matrix
