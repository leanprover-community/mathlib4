/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Transvection
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

section JMatrixLemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

@[simp]
theorem map_J {R S : Type*} [CommRing S] [CommRing R] (f : R →+* S) :
    (J l R).map f = J l S := by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J, fromBlocks_transpose, ← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l ⊕ l) (l ⊕ l) R),
    fromBlocks_smul, Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [fromBlocks]

variable [Fintype l]

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

/-- The group of symplectic matrices over a ring `R`. -/
def symplecticGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    exact ha
  one_mem' := by simp

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

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

theorem map_mem {S : Type*} [CommRing S]
    (f : R →+* S) (hA : A ∈ symplecticGroup l R) :
    f.mapMatrix A ∈ symplecticGroup l S := by
  rw [mem_iff] at hA ⊢
  rw [RingHom.mapMatrix_apply, ← map_J _ f, ← transpose_map,
    ← Matrix.map_mul, ← Matrix.map_mul, hA]

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

private lemma det_one_if_fromBlocks_invertible [Invertible A]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    (fromBlocks A B C D).det = 1 := by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, ← A.det_transpose, ← det_mul,
    mul_sub, ← mul_assoc, ← mul_assoc, h_block.1, mul_assoc Cᵀ,
    mul_inv_of_invertible, mul_one, h_block.2.2, det_one]

private lemma ker_inter_eq_bot_of_rank_normal_form
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h_rank : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0) (x : l → R)
    (h1 : (Vᵀ⁻¹ * A * U) • x = 0) (h2 : (V * C * U) • x = 0) : x = 0 := by
  refine (U.isUnit_iff_isUnit_det.2 hU).smul_left_cancel.1 ?_
  rw [mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul] at h1 h2
  all_goals simp_all [isUnit_iff_isUnit_det]

private lemma symm_condition_of_rank_normal_form (hV : IsUnit V.det)
    (h_symm : Aᵀ * C = Cᵀ * A) :
    (Vᵀ⁻¹ * A * U)ᵀ * (V * C * U) = (V * C * U)ᵀ * (Vᵀ⁻¹ * A * U) := by
  rw [transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    transpose_nonsing_inv, transpose_transpose]
  convert_to Uᵀ * (Aᵀ * (V⁻¹ * V) * C * U) = Uᵀ * (Cᵀ * (Vᵀ * Vᵀ⁻¹) * A * U)
  · ac_rfl
  · ac_rfl
  · rw [V.nonsing_inv_mul hV, mul_nonsing_inv _ (V.isUnit_det_transpose hV),
      mul_one, mul_one, h_symm]

private lemma eq_zero_and_symm_on_support_of_diagonal_symm {s : Finset l}
    (hR1 : let E : Matrix l l R := diagonal (fun i : l ↦ if i ∈ s then 1 else 0)
      Aᵀ * E = E * A) :
    (∀ (i j : l), i ∈ s → j ∉ s → A i j = 0) ∧
    (∀ (i j : l), i ∈ s → j ∈ s → A i j = A j i) := by
  have h_main1 (i j : l) : (if j ∈ s then A j i else 0) = (if i ∈ s then A i j else 0) := by
    convert ext_iff.2 hR1 i j <;> simp
  constructor <;> intro i j hi hj
  · have := (h_main1 i j).symm
    rwa [if_pos hi, if_neg hj] at this
  · have := (h_main1 i j).symm
    rwa [if_pos hj, if_pos hi] at this

private lemma exists_symmetric_X_invertible_add_mul_diagonal {R : Type*} [Field R] {s : Finset l}
    {A : Matrix l l R} (h1 : ∀ (i j : l), i ∈ s → j ∉ s → A i j = 0)
    (h2 : ∀ (i j : l), i ∈ s → j ∈ s → A i j = A j i)
    (h_rank1 : ∀ (x : l → R), (A • x = 0) →
      ((diagonal (fun i ↦ if i ∈ s then 1 else (0 : R))) • x = 0) → x = 0) :
    ∃ (X : Matrix l l R), X.IsSymm ∧
      IsUnit (A + X * (diagonal (fun i : l ↦ if i ∈ s then 1 else 0))).det := by
  set D : Matrix l l R := diagonal (fun i : l ↦ if i ∈ s then 1 else 0) with D_def
  set X : Matrix l l R := fun i j ↦
    if i ∈ s ∧ j ∈ s then (if i = j then 1 else 0) - A i j else 0 with X1_def
  have hX_symm : X.IsSymm := by
    ext i j
    simp only [X1_def, transpose_apply]; grind
  have hM1 (i : l) (hi : i ∈ s) (j : l) : (A + X * D) i j = if i = j then 1 else 0 := by
    simp only [X1_def, D_def, Matrix.add_apply, mul_diagonal, mul_ite, mul_one, mul_zero]; grind
  set M := A + X * D with M_def
  refine ⟨X, hX_symm, M.isUnit_iff_isUnit_det.1 <|
    isUnit_toLin'_iff.1 <| M.toLin'.isUnit_iff_ker_eq_bot.2 <|
      ker_toLin'_eq_bot_iff.2 <| fun x hx ↦ ?_⟩
  have hDx : D • x = 0 := by
    ext i
    convert_to (if i ∈ s then x i else 0) = _
    · simp [D_def, Finset.sum_ite_eq, mulVec_apply, diagonal_apply]
    · refine ite_eq_right_iff.2 fun hi ↦ ?_
      simpa [hM1 i hi] using (show ∑ j : l, M i j * x j = 0 from congrFun hx i)
  have hAx : A • x = 0 := by
    convert_to A • x + (X * D) • x = 0
    · rw [left_eq_add, mul_smul, hDx, smul_zero]
    · rwa [← add_smul]
  exact h_rank1 x hAx hDx

private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (h_rank : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (h_symm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, hR1_eq⟩
  set C' := V * C * U with C'_def
  set D := diagonal (fun i ↦ if i ∈ s then 1 else 0) with D_def
  set A' := Vᵀ⁻¹ * A * U with A'_def
  have h_main1 : (∀ (i j : l), i ∈ s → j ∉ s → A' i j = 0) ∧
      (∀ (i j : l), i ∈ s → j ∈ s → A' i j = A' j i) := by
    refine eq_zero_and_symm_on_support_of_diagonal_symm ?_
    have h_symm1 : A'ᵀ * C' = C'ᵀ * A' := symm_condition_of_rank_normal_form hV h_symm
    rwa [hR1_eq, diagonal_transpose] at h_symm1
  obtain ⟨X, hX_symm, hM1⟩ := exists_symmetric_X_invertible_add_mul_diagonal
    h_main1.1 h_main1.2 <| fun x hP1x hDx ↦
      ker_inter_eq_bot_of_rank_normal_form hU hV h_rank x hP1x (hR1_eq ▸ hDx : C' *ᵥ x = 0)
  refine ⟨Vᵀ * X * V, ?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_mul, hX_symm, transpose_transpose, mul_assoc]
  · convert_to IsUnit (Vᵀ * (A' + X * C') * U⁻¹).det
    · simp [U.mul_nonsing_inv_cancel_right _ hU, mul_add, add_mul, mul_assoc, A'_def, C'_def,
        Vᵀ.mul_nonsing_inv_cancel_left _ (V.isUnit_det_transpose hV)]
    rw [det_mul, det_mul, hR1_eq]
    exact ((det_transpose V ▸ hV).mul hM1).mul <| U.isUnit_nonsing_inv_det hU

private lemma exists_symmetric_X_isUnit_det_add_mul_of_symplectic [IsLocalRing R]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set B' := f.mapMatrix B
  set C' := f.mapMatrix C; set D' := f.mapMatrix D
  set F' := fromBlocks A' B' C' D' with F'_def
  have h15' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have h_rank (x : l → k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    set v : l ⊕ l → k := Sum.elim x (fun _ ↦ 0) with v_def
    have h_v0 : F' *ᵥ v = 0 := by
      ext s; cases s with
      | inl i =>
        rw [mulVec_apply, Fintype.sum_sum_type, Finset.sum_congr rfl fun _ _ ↦ rfl]
        simp only [F'_def, fromBlocks, of_apply, Sum.elim_inl, v_def, Sum.elim_inr, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply]
        rw [← mulVec_apply, hx1, Pi.zero_apply]
      | inr i =>
        rw [mulVec_apply, Fintype.sum_sum_type, Finset.sum_congr rfl fun _ _ ↦ rfl]
        simp only [F'_def, fromBlocks_apply₂₁, v_def, Sum.elim_inl, fromBlocks_apply₂₂,
          Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, Pi.zero_apply]
        rw [← mulVec_apply, hx2, Pi.zero_apply]
    funext i
    convert_to v (Sum.inl i) = _
    · rw [v_def, Sum.elim_inl]
    · exact congrFun (mulVec_injective_iff_isUnit.2 h15' (F'.mulVec_zero.symm ▸ h_v0)) _
  obtain ⟨Y, hY_symm, hXbar_det⟩ :=
    exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot h_rank <| by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul, (fromBlocks_mem_iff.1 hA).1, map_mul]
  obtain ⟨X, hX_symm, hXY⟩ := hY_symm.exists_map_eq_of_surjective IsLocalRing.residue_surjective
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply _ X, hXY]
  exact hXbar_det.ne_zero

/-- Over any local ring, every symplectic matrix has determinant 1. -/
private lemma det_eq_one_of_isLocalRing [IsLocalRing R] {M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M ∈ symplecticGroup l R) : M.det = 1 := by
  let A : Matrix l l R := fun i j ↦ M (Sum.inl i) (Sum.inl j)
  let B : Matrix l l R := fun i j ↦ M (Sum.inl i) (Sum.inr j)
  let C : Matrix l l R := fun i j ↦ M (Sum.inr i) (Sum.inl j)
  let D : Matrix l l R := fun i j ↦ M (Sum.inr i) (Sum.inr j)
  have hM_blocks : M = fromBlocks A B C D := by
    ext i j; cases i <;> cases j <;> rfl
  obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    <| hM_blocks ▸ hM
  set Lx : Matrix (l ⊕ l) (l ⊕ l) R := fromBlocks 1 X 0 1 with Lx_def
  have Lx_mul : Lx * fromBlocks A B C D = fromBlocks (A + X * C) (B + X * D) C D := by
    simp [Lx_def, fromBlocks_multiply]
  set M' : Matrix (l ⊕ l) (l ⊕ l) R := Lx * M with M'_def
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D ∈ symplecticGroup l R := by
    rw [← Lx_mul, ← hM_blocks, ← M'_def]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, Lx_def, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  have h_main : M'.det = 1 := by
    rw [M'_def, hM_blocks, Lx_mul, det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main

/-- Symplectic matrices have determinant 1. -/
theorem det_eq_one {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) :
    M.det = 1 := by
  refine sub_eq_zero.1 <| eq_zero_of_localization _ fun _ _ ↦ ?_
  rw [map_sub, RingHom.map_det, det_eq_one_of_isLocalRing <| map_mem _ hM, map_one, sub_self]

end Determinant

end SymplecticGroup
