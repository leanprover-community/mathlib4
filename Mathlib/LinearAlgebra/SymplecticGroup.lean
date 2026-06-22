/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery, Seed Prover
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## TODO
* For `n = 1` the symplectic group coincides with the special linear group.
-/

@[expose] public section


open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The group of symplectic matrices over a ring `R`. -/
def symplecticGroup [Fintype l] : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    exact ha
  one_mem' := by simp

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [CommRing R]

open Matrix

section JMatrixLemmas

@[simp]
theorem map_J {F S : Type*} [CommRing S] [FunLike F R S]
    [AddMonoidHomClass F R S] [OneHomClass F R S] (f : F) :
    (J l R).map f = J l S := by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J, fromBlocks_transpose, ← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l ⊕ l) (l ⊕ l) R),
    fromBlocks_smul, Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [fromBlocks]

variable (l) (R) [Fintype l]

theorem J_squared : J l R * J l R = -1 := by
  rw [J, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero, ← Matrix.fromBlocks_neg, ← fromBlocks_one]

theorem J_inv : (J l R)⁻¹ = -J l R := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, J_squared]
  exact neg_neg 1

theorem J_det_mul_J_det : det (J l R) * det (J l R) = 1 := by
  rw [← det_mul, J_squared, ← one_smul R (-1 : Matrix _ _ R), smul_neg, ← neg_smul, det_smul,
    Fintype.card_sum, det_one, mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _

theorem isUnit_det_J : IsUnit (det (J l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

end JMatrixLemmas

variable [Fintype l]

theorem mem_iff {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ A * J l R * Aᵀ = J l R := by simp [symplecticGroup]

instance coeMatrix : Coe (symplecticGroup l R) (Matrix (l ⊕ l) (l ⊕ l) R) :=
  ⟨Subtype.val⟩

section SymplecticJ

variable (l) (R)

theorem J_mem : J l R ∈ symplecticGroup l R := by
  rw [mem_iff, J, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_multiply]
  simp

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
def symJ : symplecticGroup l R :=
  ⟨J l R, J_mem l R⟩

variable {l} {R}

@[simp]
theorem coe_J : ↑(symJ l R) = J l R := rfl

end SymplecticJ

variable {A : Matrix (l ⊕ l) (l ⊕ l) R}

theorem neg_mem (h : A ∈ symplecticGroup l R) : -A ∈ symplecticGroup l R := by
  rw [mem_iff] at h ⊢
  simp [h]

theorem symplectic_det (hA : A ∈ symplecticGroup l R) : IsUnit <| det A := by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det, mul_assoc] at hA
  exact hA

theorem map_mem {F S : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (hA : A ∈ symplecticGroup l R) : A.map f ∈ symplecticGroup l S := by
  simp_rw [mem_iff, ← transpose_map, ← map_J f, ← Matrix.map_mul, mem_iff.mp hA]

theorem transpose_mem (hA : A ∈ symplecticGroup l R) : Aᵀ ∈ symplecticGroup l R := by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
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

@[simp]
theorem transpose_mem_iff : Aᵀ ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩

theorem mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ * J l R * A = J l R := by
  rw [← transpose_mem_iff, mem_iff, transpose_transpose]

instance hasInv : Inv (symplecticGroup l R) where
  inv A := ⟨(-J l R) * (A : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R,
      mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) <| J_mem _ _⟩

theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R := rfl

theorem inv_left_mul_aux (hA : A ∈ symplecticGroup l R) : -(J l R * Aᵀ * J l R * A) = 1 :=
  calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]

theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R) = (↑A)⁻¹ := by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]

theorem inv_eq_symplectic_inv (A : Matrix (l ⊕ l) (l ⊕ l) R) (hA : A ∈ symplecticGroup l R) :
    A⁻¹ = (-J l R) * Aᵀ * J l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])

instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

theorem fromBlocks_mem_iff [Finite l] {A B C D : Matrix l l R} :
    fromBlocks A B C D ∈ symplecticGroup l R ↔
      Aᵀ * C = Cᵀ * A ∧
      Bᵀ * D = Dᵀ * B ∧
      Aᵀ * D - Cᵀ * B = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_iff'.2 ?_⟩
  · have h_final : fromBlocks (Cᵀ * A - Aᵀ * C) (Cᵀ * B - Aᵀ * D)
        (Dᵀ * A - Bᵀ * C) (Dᵀ * B - Bᵀ * D) = J l R := by
      simpa [mem_iff, fromBlocks_transpose, J, fromBlocks_multiply,
        sub_eq_add_neg] using transpose_mem h
    obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
    exact ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, by grind⟩
  · simp only [fromBlocks_transpose, J, fromBlocks_multiply, mul_zero, mul_one, zero_add, mul_neg,
      add_zero, neg_mul, ← sub_eq_add_neg, fromBlocks_inj, sub_eq_zero]
    exact ⟨h.1.symm, by grind, by simpa using congr(transpose $(h.2.2)), h.2.1.symm⟩

section Determinant

variable {A B C D U V : Matrix l l R}

/-- Schur-complement step: a symplectic block matrix has determinant `1` once its upper-left
block is invertible. -/
private lemma det_one_if_fromBlocks_invertible [Invertible A]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    (fromBlocks A B C D).det = 1 := by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, ← A.det_transpose, ← det_mul,
    mul_sub, ← mul_assoc, ← mul_assoc, h_block.1, mul_assoc Cᵀ,
    mul_inv_of_invertible, mul_one, h_block.2.2, det_one]

/-- Field normal-form step: under the kernel-intersection and symmetry hypotheses, construct
a symmetric shear `X` such that `A + X * C` is invertible. -/
private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (h_rank : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (h_symm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have hf_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have hf_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (hf_unit (V.isUnit_transpose.2 hV)).invertible
  -- The kernel-intersection hypothesis survives this change of coordinates.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → R)
      (heq1 : (f (Vᵀ⁻¹ * A * U)) • x = 0) (heq2 : (f (V * C * U)) • x = 0) : x = 0 := by
    refine (hf_unit hU).smul_left_cancel.1 ?_
    rw [hf_mul, hf_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using h_rank _ heq1 heq2
    · exact hf_unit hV
    · exact hf_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation is also invariant under the same change of coordinates.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, h_symm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, hf_mul, hf_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The remaining lower-right block of `Q` is invertible by the transformed kernel condition.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [← P_def, hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  set X := (f Vᵀ) * Y * (f V) with X_def
  have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
    simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, hf_mul, hf, mul_add, ← mul_assoc,
      ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
    simp [X_def]; rfl
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact hf_unit <| isUnit_nonsing_inv_iff.2 hU

/-- Local lifting step: reduce a symplectic block matrix to the residue field, apply the field
normal-form step there, then lift the symmetric shear back to the local ring. -/
private lemma exists_symmetric_X_isUnit_det_add_mul_of_symplectic [IsLocalRing R]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have h_rank (x : l → k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have h_v0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' h_v0)).1
  obtain ⟨Y, hY_symm, hY_det⟩ :=
    exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot h_rank <| by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul, (fromBlocks_mem_iff.1 hA).1, map_mul]
  obtain ⟨X, hX_symm, hXY⟩ : ∃ X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j ↦ hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply _ X, hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

/-- Local determinant step: after a symmetric shear makes the upper-left block invertible, the
Schur-complement step proves the determinant is `1`. -/
private lemma det_eq_one_of_isLocalRing [IsLocalRing R] {M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M ∈ symplecticGroup l R) : M.det = 1 := by
  set A := M.toBlocks₁₁; set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁; set D := M.toBlocks₂₂
  obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic <|
    M.fromBlocks_toBlocks ▸ hM
  have Lx_mul : (fromBlocks 1 X 0 1) * M = fromBlocks (A + X * C) (B + X * D) C D := by
    rw [← M.fromBlocks_toBlocks, fromBlocks_multiply]
    simp only [one_mul, zero_mul, zero_add]; rfl
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D ∈ symplecticGroup l R := by
    rw [← Lx_mul]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  have h_main : ((fromBlocks 1 X 0 1) * M).det = 1 := by
    rw [Lx_mul, det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main

/-- Symplectic matrices have determinant 1. -/
theorem det_eq_one {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) :
    M.det = 1 := by
  refine sub_eq_zero.1 <| eq_zero_of_localization _ fun _ _ ↦ ?_
  simp [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_one_of_isLocalRing <| map_mem _ hM]

end Determinant

end SymplecticGroup
