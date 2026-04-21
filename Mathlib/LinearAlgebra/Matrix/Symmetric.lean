/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

* `Matrix.isSymm`: a matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/

@[expose] public section


variable {α β n m R : Type*}

namespace Matrix

/-- A matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`. -/
def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A

instance (A : Matrix n n α) [Decidable (Aᵀ = A)] : Decidable (IsSymm A) :=
  inferInstanceAs <| Decidable (_ = _)

theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A :=
  h

/-- A version of `Matrix.ext_iff` that unfolds the `Matrix.transpose`. -/
theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j :=
  Matrix.ext_iff.symm

/-- A version of `Matrix.ext` that unfolds the `Matrix.transpose`. -/
theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm :=
  Matrix.ext

theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
  IsSymm.ext_iff.1 h i j

theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (A * Aᵀ).IsSymm :=
  transpose_mul _ _

theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (Aᵀ * A).IsSymm :=
  transpose_mul _ _

theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
  add_comm _ _

theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
  add_comm _ _

@[simp]
theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm :=
  transpose_zero

@[simp]
theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm :=
  transpose_one

theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
    (k : ℕ) :
    (A ^ k).IsSymm := by
  rw [IsSymm, transpose_pow, h]

@[simp]
theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α → β) : (A.map f).IsSymm := by
  rw [IsSymm, ← transpose_map, h.eq]

@[simp]
theorem isSymm_map_iff {A : Matrix n n α} {f : α → β} (hf : f.Injective) :
    (A.map f).IsSymm ↔ A.IsSymm := by
  rw [IsSymm, IsSymm, ← transpose_map, map_injective hf |>.eq_iff]

theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm :=
  congr_arg _ h

@[simp]
theorem isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

@[simp]
theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm :=
  h.transpose.map _

@[simp]
theorem isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

@[simp]
theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm :=
  (transpose_neg _).trans (congr_arg _ h)

@[simp]
theorem isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]
theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
  (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
  (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
  (transpose_smul _ _).trans (congr_arg _ h)

@[simp]
theorem isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k] :
    (k • A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

@[simp]
theorem IsSymm.submatrix {A : Matrix n n α} (h : A.IsSymm) (f : m → n) : (A.submatrix f f).IsSymm :=
  (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

theorem IsSymm.reindex {A : Matrix n n α} (h : A.IsSymm) (f : n ≃ m) : (A.reindex f f).IsSymm := by
  rw [reindex_apply]
  apply submatrix h

theorem isSymm_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp]
theorem isSymm_diagonal [DecidableEq n] [Zero α] (v : n → α) : (diagonal v).IsSymm :=
  diagonal_transpose _

/-- A block matrix `A.fromBlocks B C D` is symmetric,
if `A` and `D` are symmetric and `Bᵀ = C`. -/
theorem IsSymm.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsSymm) (hBC : Bᵀ = C) (hD : D.IsSymm) :
    (A.fromBlocks B C D).IsSymm := by
  have hCB : Cᵀ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose, hA, hCB, hBC, hD]

/-- This is the `iff` version of `Matrix.isSymm.fromBlocks`. -/
theorem isSymm_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsSymm ↔ A.IsSymm ∧ Bᵀ = C ∧ Cᵀ = B ∧ D.IsSymm :=
  ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
      (congr_arg toBlocks₂₂ h :)⟩,
    fun ⟨hA, hBC, _, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩

theorem isSymm_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ Aᵀ = A.map (·ᵀ) := by
  rw [IsSymm, transpose_comp, transpose_map, comp .. |>.injective.eq_iff, eq_comm,
    transpose_involutive _ _ |>.eq_iff]

theorem isSymm_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ ∀ i j i' j', A j i j' i' = A i j i' j' := by
  simp [IsSymm.ext_iff]
  grind

end Matrix
