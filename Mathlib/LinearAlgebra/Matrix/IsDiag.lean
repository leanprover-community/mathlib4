/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Data.Matrix.Kronecker

/-!
# Diagonal matrices

This file contains the definition and basic results about diagonal matrices.

## Main results

- `Matrix.IsDiag`: a proposition that states a given square matrix `A` is diagonal.

## Tags

diag, diagonal, matrix
-/


namespace Matrix

variable {α β R n m : Type*}

open Function

open Matrix Kronecker

/-- `A.IsDiag` means square matrix `A` is a diagonal matrix. -/
def IsDiag [Zero α] (A : Matrix n n α) : Prop :=
  Pairwise fun i j => A i j = 0

@[simp]
theorem isDiag_diagonal [Zero α] [DecidableEq n] (d : n → α) : (diagonal d).IsDiag := fun _ _ =>
  Matrix.diagonal_apply_ne _

/-- Diagonal matrices are generated by the `Matrix.diagonal` of their `Matrix.diag`. -/
theorem IsDiag.diagonal_diag [Zero α] [DecidableEq n] {A : Matrix n n α} (h : A.IsDiag) :
    diagonal (diag A) = A :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [diagonal_apply_eq, diag]
    · rw [diagonal_apply_ne _ hij, h hij]

/-- `Matrix.IsDiag.diagonal_diag` as an iff. -/
theorem isDiag_iff_diagonal_diag [Zero α] [DecidableEq n] (A : Matrix n n α) :
    A.IsDiag ↔ diagonal (diag A) = A :=
  ⟨IsDiag.diagonal_diag, fun hd => hd ▸ isDiag_diagonal (diag A)⟩

/-- Every matrix indexed by a subsingleton is diagonal. -/
theorem isDiag_of_subsingleton [Zero α] [Subsingleton n] (A : Matrix n n α) : A.IsDiag :=
  fun i j h => (h <| Subsingleton.elim i j).elim

/-- Every zero matrix is diagonal. -/
@[simp]
theorem isDiag_zero [Zero α] : (0 : Matrix n n α).IsDiag := fun _ _ _ => rfl

/-- Every identity matrix is diagonal. -/
@[simp]
theorem isDiag_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsDiag := fun _ _ =>
  one_apply_ne

theorem IsDiag.map [Zero α] [Zero β] {A : Matrix n n α} (ha : A.IsDiag) {f : α → β} (hf : f 0 = 0) :
    (A.map f).IsDiag := by
  intro i j h
  simp [ha h, hf]

theorem IsDiag.neg [AddGroup α] {A : Matrix n n α} (ha : A.IsDiag) : (-A).IsDiag := by
  intro i j h
  simp [ha h]

@[simp]
theorem isDiag_neg_iff [AddGroup α] {A : Matrix n n α} : (-A).IsDiag ↔ A.IsDiag :=
  ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), IsDiag.neg⟩

theorem IsDiag.add [AddZeroClass α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A + B).IsDiag := by
  intro i j h
  simp [ha h, hb h]

theorem IsDiag.sub [AddGroup α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A - B).IsDiag := by
  intro i j h
  simp [ha h, hb h]

theorem IsDiag.smul [Monoid R] [AddMonoid α] [DistribMulAction R α] (k : R) {A : Matrix n n α}
    (ha : A.IsDiag) : (k • A).IsDiag := by
  intro i j h
  simp [ha h]

@[simp]
theorem isDiag_smul_one (n) [Semiring α] [DecidableEq n] (k : α) :
    (k • (1 : Matrix n n α)).IsDiag :=
  isDiag_one.smul k

theorem IsDiag.transpose [Zero α] {A : Matrix n n α} (ha : A.IsDiag) : Aᵀ.IsDiag := fun _ _ h =>
  ha h.symm

@[simp]
theorem isDiag_transpose_iff [Zero α] {A : Matrix n n α} : Aᵀ.IsDiag ↔ A.IsDiag :=
  ⟨IsDiag.transpose, IsDiag.transpose⟩

theorem IsDiag.conjTranspose [Semiring α] [StarRing α] {A : Matrix n n α} (ha : A.IsDiag) :
    Aᴴ.IsDiag :=
  ha.transpose.map (star_zero _)

@[simp]
theorem isDiag_conjTranspose_iff [Semiring α] [StarRing α] {A : Matrix n n α} :
    Aᴴ.IsDiag ↔ A.IsDiag :=
  ⟨fun ha => by
    convert ha.conjTranspose
    simp, IsDiag.conjTranspose⟩

theorem IsDiag.submatrix [Zero α] {A : Matrix n n α} (ha : A.IsDiag) {f : m → n}
    (hf : Injective f) : (A.submatrix f f).IsDiag := fun _ _ h => ha (hf.ne h)

/-- `(A ⊗ B).IsDiag` if both `A` and `B` are diagonal. -/
theorem IsDiag.kronecker [MulZeroClass α] {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsDiag)
    (hB : B.IsDiag) : (A ⊗ₖ B).IsDiag := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.inj_iff, Ne, not_and_or] at h
  rcases h with hac | hbd
  · simp [hA hac]
  · simp [hB hbd]

theorem IsDiag.isSymm [Zero α] {A : Matrix n n α} (h : A.IsDiag) : A.IsSymm := by
  ext i j
  by_cases g : i = j; · rw [g, transpose_apply]
  simp [h g, h (Ne.symm g)]

/-- The block matrix `A.fromBlocks 0 0 D` is diagonal if `A` and `D` are diagonal. -/
theorem IsDiag.fromBlocks [Zero α] {A : Matrix m m α} {D : Matrix n n α} (ha : A.IsDiag)
    (hd : D.IsDiag) : (A.fromBlocks 0 0 D).IsDiag := by
  rintro (i | i) (j | j) hij
  · exact ha (ne_of_apply_ne _ hij)
  · rfl
  · rfl
  · exact hd (ne_of_apply_ne _ hij)

/-- This is the `iff` version of `Matrix.IsDiag.fromBlocks`. -/
theorem isDiag_fromBlocks_iff [Zero α] {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsDiag ↔ A.IsDiag ∧ B = 0 ∧ C = 0 ∧ D.IsDiag := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ext fun i j => ?_, ext fun i j => ?_, fun i j hij => ?_⟩
    · exact h (Sum.inl_injective.ne hij)
    · exact h Sum.inl_ne_inr
    · exact h Sum.inr_ne_inl
    · exact h (Sum.inr_injective.ne hij)
  · rintro ⟨ha, hb, hc, hd⟩
    convert IsDiag.fromBlocks ha hd

/-- A symmetric block matrix `A.fromBlocks B C D` is diagonal
    if `A` and `D` are diagonal and `B` is `0`. -/
theorem IsDiag.fromBlocks_of_isSymm [Zero α] {A : Matrix m m α} {C : Matrix n m α}
    {D : Matrix n n α} (h : (A.fromBlocks 0 C D).IsSymm) (ha : A.IsDiag) (hd : D.IsDiag) :
    (A.fromBlocks 0 C D).IsDiag := by
  rw [← (isSymm_fromBlocks_iff.1 h).2.1]
  exact ha.fromBlocks hd

theorem mul_transpose_self_isDiag_iff_hasOrthogonalRows [Fintype n] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (A * Aᵀ).IsDiag ↔ A.HasOrthogonalRows :=
  Iff.rfl

theorem transpose_mul_self_isDiag_iff_hasOrthogonalCols [Fintype m] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (Aᵀ * A).IsDiag ↔ A.HasOrthogonalCols :=
  Iff.rfl

end Matrix
