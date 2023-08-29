/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

#align_import linear_algebra.symplectic_group from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## TODO
* Every symplectic matrix has determinant 1.
* For `n = 1` the symplectic group coincides with the special linear group.
-/


open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 (-1) 1 0
set_option linter.uppercaseLean3 false in
#align matrix.J Matrix.J

@[simp]
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J, fromBlocks_transpose, ← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l ⊕ l) (l ⊕ l) R),
    fromBlocks_smul, Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [fromBlocks]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align matrix.J_transpose Matrix.J_transpose

variable [Fintype l]

theorem J_squared : J l R * J l R = -1 := by
  rw [J, fromBlocks_multiply]
  -- ⊢ fromBlocks (0 * 0 + -1 * 1) (0 * -1 + -1 * 0) (1 * 0 + 0 * 1) (1 * -1 + 0 *  …
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  -- ⊢ fromBlocks (-1) 0 0 (-1) = -1
  rw [← neg_zero, ← Matrix.fromBlocks_neg, ← fromBlocks_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align matrix.J_squared Matrix.J_squared

theorem J_inv : (J l R)⁻¹ = -J l R := by
  refine' Matrix.inv_eq_right_inv _
  -- ⊢ J l R * -J l R = 1
  rw [Matrix.mul_neg, J_squared]
  -- ⊢ - -1 = 1
  exact neg_neg 1
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align matrix.J_inv Matrix.J_inv

theorem J_det_mul_J_det : det (J l R) * det (J l R) = 1 := by
  rw [← det_mul, J_squared, ← one_smul R (-1 : Matrix _ _ R), smul_neg, ← neg_smul, det_smul,
    Fintype.card_sum, det_one, mul_one]
  apply Even.neg_one_pow
  -- ⊢ Even (Fintype.card l + Fintype.card l)
  exact even_add_self _
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align matrix.J_det_mul_J_det Matrix.J_det_mul_J_det

theorem isUnit_det_J : IsUnit (det (J l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩
set_option linter.uppercaseLean3 false in
#align matrix.is_unit_det_J Matrix.isUnit_det_J

end JMatrixLemmas

variable [Fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
def symplecticGroup : Submonoid (Matrix (Sum l l) (Sum l l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, transpose_mul] at *
    -- ⊢ a * b * J l R * (bᵀ * aᵀ) = J l R
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    -- ⊢ a * J l R * aᵀ = J l R
    exact ha
    -- 🎉 no goals
  one_mem' := by simp
                 -- 🎉 no goals
#align matrix.symplectic_group Matrix.symplecticGroup

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

theorem mem_iff {A : Matrix (Sum l l) (Sum l l) R} :
    A ∈ symplecticGroup l R ↔ A * J l R * Aᵀ = J l R := by simp [symplecticGroup]
                                                           -- 🎉 no goals
#align symplectic_group.mem_iff SymplecticGroup.mem_iff

-- Porting note: Previous proof was `by infer_instance`
instance coeMatrix : Coe (symplecticGroup l R) (Matrix (Sum l l) (Sum l l) R) :=
  ⟨Subtype.val⟩
#align symplectic_group.coe_matrix SymplecticGroup.coeMatrix

section SymplecticJ

variable (l) (R)

theorem J_mem : J l R ∈ symplecticGroup l R := by
  rw [mem_iff, J, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_multiply]
  -- ⊢ fromBlocks ((0 * 0 + -1 * 1) * 0ᵀ + (0 * -1 + -1 * 0) * (-1)ᵀ) ((0 * 0 + -1  …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align symplectic_group.J_mem SymplecticGroup.J_mem

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
def symJ : symplecticGroup l R :=
  ⟨J l R, J_mem l R⟩
set_option linter.uppercaseLean3 false in
#align symplectic_group.sym_J SymplecticGroup.symJ

variable {l} {R}

@[simp]
theorem coe_J : ↑(symJ l R) = J l R := rfl
set_option linter.uppercaseLean3 false in
#align symplectic_group.coe_J SymplecticGroup.coe_J

end SymplecticJ

variable {A : Matrix (Sum l l) (Sum l l) R}

theorem neg_mem (h : A ∈ symplecticGroup l R) : -A ∈ symplecticGroup l R := by
  rw [mem_iff] at h ⊢
  -- ⊢ -A * J l R * (-A)ᵀ = J l R
  simp [h]
  -- 🎉 no goals
#align symplectic_group.neg_mem SymplecticGroup.neg_mem

theorem symplectic_det (hA : A ∈ symplecticGroup l R) : IsUnit <| det A := by
  rw [isUnit_iff_exists_inv]
  -- ⊢ ∃ b, det A * b = 1
  use A.det
  -- ⊢ det A * det A = 1
  refine' (isUnit_det_J l R).mul_left_cancel _
  -- ⊢ det (J l R) * (det A * det A) = det (J l R) * 1
  rw [mul_one]
  -- ⊢ det (J l R) * (det A * det A) = det (J l R)
  rw [mem_iff] at hA
  -- ⊢ det (J l R) * (det A * det A) = det (J l R)
  apply_fun det at hA
  -- ⊢ det (J l R) * (det A * det A) = det (J l R)
  simp only [det_mul, det_transpose] at hA
  -- ⊢ det (J l R) * (det A * det A) = det (J l R)
  rw [mul_comm A.det, mul_assoc] at hA
  -- ⊢ det (J l R) * (det A * det A) = det (J l R)
  exact hA
  -- 🎉 no goals
#align symplectic_group.symplectic_det SymplecticGroup.symplectic_det

theorem transpose_mem (hA : A ∈ symplecticGroup l R) : Aᵀ ∈ symplecticGroup l R := by
  rw [mem_iff] at hA ⊢
  -- ⊢ Aᵀ * J l R * Aᵀᵀ = J l R
  rw [transpose_transpose]
  -- ⊢ Aᵀ * J l R * A = J l R
  have huA := symplectic_det hA
  -- ⊢ Aᵀ * J l R * A = J l R
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]
#align symplectic_group.transpose_mem SymplecticGroup.transpose_mem

@[simp]
theorem transpose_mem_iff : Aᵀ ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩
                -- 🎉 no goals
#align symplectic_group.transpose_mem_iff SymplecticGroup.transpose_mem_iff

theorem mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ * J l R * A = J l R := by
  rw [← transpose_mem_iff, mem_iff, transpose_transpose]
  -- 🎉 no goals
#align symplectic_group.mem_iff' SymplecticGroup.mem_iff'

instance hasInv : Inv (symplecticGroup l R) where
  inv A := ⟨(-J l R) * (A : Matrix (Sum l l) (Sum l l) R)ᵀ * J l R,
      mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) <| J_mem _ _⟩

theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R := rfl
#align symplectic_group.coe_inv SymplecticGroup.coe_inv

theorem inv_left_mul_aux (hA : A ∈ symplecticGroup l R) : -(J l R * Aᵀ * J l R * A) = 1 :=
  calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
      -- 🎉 no goals
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      -- ⊢ -J l R * (Aᵀ * J l R * A) = -J l R * J l R
      rw [hA]
      -- 🎉 no goals
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
                                         -- 🎉 no goals
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
                                             -- 🎉 no goals
    _ = 1 := by simp only [neg_smul_neg, one_smul]
                -- 🎉 no goals
#align symplectic_group.inv_left_mul_aux SymplecticGroup.inv_left_mul_aux

theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (Sum l l) (Sum l l) R) = (↑A)⁻¹ := by
  refine' (coe_inv A).trans (inv_eq_left_inv _).symm
  -- ⊢ -J l R * (↑A)ᵀ * J l R * ↑A = 1
  simp [inv_left_mul_aux, coe_inv]
  -- 🎉 no goals
#align symplectic_group.coe_inv' SymplecticGroup.coe_inv'

theorem inv_eq_symplectic_inv (A : Matrix (Sum l l) (Sum l l) R) (hA : A ∈ symplecticGroup l R) :
    A⁻¹ = (-J l R) * Aᵀ * J l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])
                      -- 🎉 no goals
#align symplectic_group.inv_eq_symplectic_inv SymplecticGroup.inv_eq_symplectic_inv

instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    mul_left_inv := fun A => by
      apply Subtype.ext
      -- ⊢ ↑(A⁻¹ * A) = ↑1
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      -- ⊢ -(J l R * (↑A)ᵀ * J l R * ↑A) = 1
      exact inv_left_mul_aux A.2 }
      -- 🎉 no goals

end SymplecticGroup
