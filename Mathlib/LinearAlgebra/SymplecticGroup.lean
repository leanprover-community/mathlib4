/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery

! This file was ported from Lean 3 source module linear_algebra.symplectic_group
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

`matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
`symplectic_group`: the group of symplectic matrices

## TODO
* Every symplectic matrix has determinant 1.
* For `n = 1` the symplectic group coincides with the special linear group.
-/


open Matrix

variable {l R : Type _}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def j : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 (-1) 1 0
#align matrix.J Matrix.j

@[simp]
theorem j_transpose : (j l R)ᵀ = -j l R :=
  by
  rw [J, from_blocks_transpose, ← neg_one_smul R (from_blocks _ _ _ _), from_blocks_smul,
    Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [from_blocks]
#align matrix.J_transpose Matrix.j_transpose

variable [Fintype l]

theorem j_squared : j l R ⬝ j l R = -1 :=
  by
  rw [J, from_blocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero, ← Matrix.fromBlocks_neg, ← from_blocks_one]
#align matrix.J_squared Matrix.j_squared

theorem j_inv : (j l R)⁻¹ = -j l R :=
  by
  refine' Matrix.inv_eq_right_inv _
  rw [Matrix.mul_neg, J_squared]
  exact neg_neg 1
#align matrix.J_inv Matrix.j_inv

theorem j_det_mul_j_det : det (j l R) * det (j l R) = 1 :=
  by
  rw [← det_mul, J_squared]
  rw [← one_smul R (-1 : Matrix _ _ R)]
  rw [smul_neg, ← neg_smul, det_smul]
  simp only [Fintype.card_sum, det_one, mul_one]
  apply Even.neg_one_pow
  exact even_add_self _
#align matrix.J_det_mul_J_det Matrix.j_det_mul_j_det

theorem isUnit_det_j : IsUnit (det (j l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (j l R), j_det_mul_j_det _ _⟩
#align matrix.is_unit_det_J Matrix.isUnit_det_j

end JMatrixLemmas

variable [Fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
def symplecticGroup : Submonoid (Matrix (Sum l l) (Sum l l) R)
    where
  carrier := { A | A ⬝ j l R ⬝ Aᵀ = j l R }
  mul_mem' := by
    intro a b ha hb
    simp only [mul_eq_mul, Set.mem_setOf_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    exact ha
  one_mem' := by simp
#align matrix.symplectic_group Matrix.symplecticGroup

end Matrix

namespace SymplecticGroup

variable {l} {R} [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

theorem mem_iff {A : Matrix (Sum l l) (Sum l l) R} :
    A ∈ symplecticGroup l R ↔ A ⬝ j l R ⬝ Aᵀ = j l R := by simp [symplectic_group]
#align symplectic_group.mem_iff SymplecticGroup.mem_iff

instance coeMatrix : Coe (symplecticGroup l R) (Matrix (Sum l l) (Sum l l) R) := by infer_instance
#align symplectic_group.coe_matrix SymplecticGroup.coeMatrix

section SymplecticJ

variable (l) (R)

theorem j_mem : j l R ∈ symplecticGroup l R :=
  by
  rw [mem_iff, J, from_blocks_multiply, from_blocks_transpose, from_blocks_multiply]
  simp
#align symplectic_group.J_mem SymplecticGroup.j_mem

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
def symJ : symplecticGroup l R :=
  ⟨j l R, j_mem l R⟩
#align symplectic_group.sym_J SymplecticGroup.symJ

variable {l} {R}

@[simp]
theorem coe_j : ↑(symJ l R) = j l R :=
  rfl
#align symplectic_group.coe_J SymplecticGroup.coe_j

end SymplecticJ

variable {R} {A : Matrix (Sum l l) (Sum l l) R}

theorem neg_mem (h : A ∈ symplecticGroup l R) : -A ∈ symplecticGroup l R :=
  by
  rw [mem_iff] at h⊢
  simp [h]
#align symplectic_group.neg_mem SymplecticGroup.neg_mem

theorem symplectic_det (hA : A ∈ symplecticGroup l R) : IsUnit <| det A :=
  by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine' (is_unit_det_J l R).mul_left_cancel _
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det  at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det, mul_assoc] at hA
  exact hA
#align symplectic_group.symplectic_det SymplecticGroup.symplectic_det

theorem transpose_mem (hA : A ∈ symplecticGroup l R) : Aᵀ ∈ symplecticGroup l R :=
  by
  rw [mem_iff] at hA⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ ⬝ J l R ⬝ A = (-Aᵀ) ⬝ (J l R)⁻¹ ⬝ A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) ⬝ (A ⬝ J l R ⬝ Aᵀ)⁻¹ ⬝ A := by rw [hA]
    _ = (-Aᵀ ⬝ (Aᵀ⁻¹ ⬝ (J l R)⁻¹)) ⬝ A⁻¹ ⬝ A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]
    
#align symplectic_group.transpose_mem SymplecticGroup.transpose_mem

@[simp]
theorem transpose_mem_iff : Aᵀ ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩
#align symplectic_group.transpose_mem_iff SymplecticGroup.transpose_mem_iff

theorem mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ ⬝ j l R ⬝ A = j l R := by
  rw [← transpose_mem_iff, mem_iff, transpose_transpose]
#align symplectic_group.mem_iff' SymplecticGroup.mem_iff'

instance : Inv (symplecticGroup l R)
    where inv A :=
    ⟨(-j l R) ⬝ (A : Matrix (Sum l l) (Sum l l) R)ᵀ ⬝ j l R,
      mul_mem (mul_mem (neg_mem <| j_mem _ _) <| transpose_mem A.2) <| j_mem _ _⟩

theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-j l R) ⬝ (↑A)ᵀ ⬝ j l R :=
  rfl
#align symplectic_group.coe_inv SymplecticGroup.coe_inv

theorem inv_left_mul_aux (hA : A ∈ symplecticGroup l R) : -j l R ⬝ Aᵀ ⬝ j l R ⬝ A = 1 :=
  calc
    -j l R ⬝ Aᵀ ⬝ j l R ⬝ A = (-j l R) ⬝ (Aᵀ ⬝ j l R ⬝ A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-j l R) ⬝ j l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • j l R ⬝ j l R := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • -1 := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]
    
#align symplectic_group.inv_left_mul_aux SymplecticGroup.inv_left_mul_aux

theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (Sum l l) (Sum l l) R) = A⁻¹ :=
  by
  refine' (coe_inv A).trans (inv_eq_left_inv _).symm
  simp [inv_left_mul_aux, coe_inv]
#align symplectic_group.coe_inv' SymplecticGroup.coe_inv'

theorem inv_eq_symplectic_inv (A : Matrix (Sum l l) (Sum l l) R) (hA : A ∈ symplecticGroup l R) :
    A⁻¹ = (-j l R) ⬝ Aᵀ ⬝ j l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])
#align symplectic_group.inv_eq_symplectic_inv SymplecticGroup.inv_eq_symplectic_inv

instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    mul_left_inv := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      rw [Matrix.mul_eq_mul, Matrix.neg_mul]
      exact inv_left_mul_aux A.2 }

end SymplecticGroup

