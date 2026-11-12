/-
Copyright (c) 2026 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/

module

public import Mathlib.LinearAlgebra.Matrix.Symmetric

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Symmetrizable Matrices

A matrix `M` is symmetrizable if there exists a diagonal matrix `D` such that `D * M` is symmetric.
If furthermore the diagonal entries of `D` are positive, `M` is said to be positively
symmetrizable.

-/

public section

namespace Matrix

variable {ι κ R : Type*} {M N : Matrix ι ι R}

/-- A matrix is symmetrizable if it is symmetric when multiplied by a diagonal matrix of diagonal
entries that do not divide zero. -/
def IsSymmetrizable [MonoidWithZero R] (M : Matrix ι ι R) : Prop :=
  ∃ d : ι → R, (∀ i, d i ∈ nonZeroDivisors R) ∧ ∀ i j, d i * M i j = d j * M j i

section IsSymmetrizable

lemma IsSymm.IsSymmetrizable [MonoidWithZero R] (h : M.IsSymm) :
    M.IsSymmetrizable := by
  use 1
  simp [h.apply]

lemma isSymmetrizable_iff [DecidableEq ι] [Fintype ι] [Semiring R] :
    M.IsSymmetrizable ↔ ∃ d : ι → R, (∀ i, d i ∈ nonZeroDivisors R) ∧ (diagonal d * M).IsSymm := by
  refine ⟨fun ⟨d, hd, h⟩ ↦ ⟨d, hd, ?_⟩, fun ⟨d, hd, h⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩⟩
  · ext i j
    rw [diagonal_mul, transpose_apply, diagonal_mul, h i j]
  · rw [← diagonal_mul, ← diagonal_mul, h.apply i j]

lemma isSymmetrizable_iff' [Field R] [DecidableEq ι] [Fintype ι] (M : Matrix ι ι R) :
    M.IsSymmetrizable ↔ ∃ d : ι → R, IsUnit (diagonal d) ∧ (diagonal d * M).IsSymm := by
  rw [isSymmetrizable_iff]
  refine ⟨fun ⟨d, hd, h⟩ ↦ ⟨d, ?_, h⟩, fun ⟨d, hd, h⟩ ↦ ⟨d, ?_, h⟩⟩
  · exact Matrix.isUnit_diagonal.mpr <|
      Pi.isUnit_iff.mpr fun i => isUnit_of_mem_nonZeroDivisors (hd i)
  · intro i
    exact (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hd) i).mem_nonZeroDivisors

lemma IsSymmetrizable.transpose [Finite ι] [CommMonoidWithZero R] (h : M.IsSymmetrizable) :
    Mᵀ.IsSymmetrizable := by
  classical
  have := Fintype.ofFinite
  obtain ⟨d, hd, h⟩ := h
  use fun i ↦ ∏ k ∈ Finset.univ.erase i, d k
  refine ⟨fun _ ↦ prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors fun a _ ↦ hd a, fun i j ↦ ?_⟩
  simp_rw [transpose_apply]
  by_cases! hij : i = j
  · rw [hij]
  have hi := Finset.prod_erase_mul (Finset.univ.erase j) d
    <| Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have hj := Finset.prod_erase_mul (Finset.univ.erase i) d
    <| Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← hj, mul_assoc, h j i, ← mul_assoc, ← hi, Finset.erase_right_comm]

lemma isSymmetrizable_transpose_iff [Finite ι] [CommMonoidWithZero R] :
    Mᵀ.IsSymmetrizable ↔ M.IsSymmetrizable :=
  ⟨transpose_transpose M ▸ .transpose, .transpose⟩

lemma IsSymmetrizable.submatrix [MonoidWithZero R] (f : κ → ι) (h : M.IsSymmetrizable) :
    (M.submatrix f f).IsSymmetrizable := by
  obtain ⟨d, hd, h⟩ := h
  use d ∘ f
  simp [hd, h]

lemma IsSymmetrizable.apply_eq_zero_iff [MonoidWithZero R] (h : M.IsSymmetrizable) {i j : ι} :
    M i j = 0 ↔ M j i = 0 := by
  obtain ⟨d, hd, h⟩ := h
  refine ⟨fun hij ↦ ?_, fun hij ↦ ?_⟩
  · exact (mem_nonZeroDivisors_iff.mp (hd j)).left (M j i) <| mul_zero (d i) ▸ hij ▸ h j i
  · exact (mem_nonZeroDivisors_iff.mp (hd i)).left (M i j) <| mul_zero (d j) ▸ hij ▸ h i j

lemma isSymmetrizable_iff_of_pairwise_eq [MonoidWithZero R] (h : Pairwise fun i j ↦ M i j = N i j) :
    M.IsSymmetrizable ↔ N.IsSymmetrizable := by
  refine ⟨fun ⟨d, hd, hM⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩, fun ⟨d, hd, hM⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩⟩
  · by_cases! hij : i = j
    · rw [hij]
    · rw [← h hij, hM, h hij.symm]
  · by_cases! hij : i = j
    · rw [hij]
    · rw [h hij, hM, h hij.symm]

@[simp]
lemma isSymmetrizable_iff_add_diagonal [DecidableEq ι] [Semiring R] (d : ι → R) :
    (M + diagonal d).IsSymmetrizable ↔ M.IsSymmetrizable := by
  rw [isSymmetrizable_iff_of_pairwise_eq]
  intro _ _ h
  simp [h]

end IsSymmetrizable

/-- A matrix is positively symmetrizable if it is symmetric when multiplied by a diagonal matrix of
positive diagonal entries. -/
def IsPosSymmetrizable [Semiring R] [LT R]
    (M : Matrix ι ι R) : Prop :=
  ∃ d : ι → R, (∀ i, 0 < d i) ∧ ∀ i j, d i * M i j = d j * M j i

section IsPosSymmetrizable

lemma IsPosSymmetrizable.isSymmetrizable [Semiring R] [IsDomain R] [Preorder R]
    (h : M.IsPosSymmetrizable) : M.IsSymmetrizable := by
  obtain ⟨d, hd, h⟩ := h
  exact ⟨d, fun i ↦ mem_nonZeroDivisors_iff_ne_zero.mpr (hd i).ne.symm, h⟩

lemma IsSymm.IsPosSymmetrizable [Semiring R] [IsDomain R] [PartialOrder R] [ZeroLEOneClass R]
    (h : M.IsSymm) :
    IsPosSymmetrizable M := by
  use 1
  simp [h.apply]

lemma isPosSymmetrizable_iff [DecidableEq ι] [Fintype ι] [Semiring R] [LT R] :
    M.IsPosSymmetrizable ↔ ∃ d : ι → R, (∀ i, 0 < d i) ∧ (diagonal d * M).IsSymm := by
  refine ⟨fun ⟨d, hd, h⟩ ↦ ⟨d, hd, ?_⟩, fun ⟨d, hd, h⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩⟩
  · ext i j
    rw [diagonal_mul, transpose_apply, diagonal_mul, h i j]
  · rw [← diagonal_mul, ← diagonal_mul, h.apply i j]

lemma IsPosSymmetrizable.transpose [Finite ι] [CommSemiring R] [IsDomain R] [PartialOrder R]
    [ZeroLEOneClass R] [PosMulStrictMono R] (h : M.IsPosSymmetrizable) :
    Mᵀ.IsPosSymmetrizable := by
  classical
  have := Fintype.ofFinite
  obtain ⟨d, hd, h⟩ := h
  use fun i ↦ ∏ k ∈ Finset.univ.erase i, d k
  refine ⟨fun _ ↦ Finset.prod_pos fun i _ ↦ hd i, ?_⟩
  intro i j
  simp only [transpose_apply]
  by_cases! hij : i = j
  · rw [hij]
  have hi := Finset.prod_erase_mul (Finset.univ.erase j) d
    <| Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have hj := Finset.prod_erase_mul (Finset.univ.erase i) d
    <| Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← hj, mul_assoc, h j i, ← mul_assoc, ← hi, Finset.erase_right_comm]

@[simp]
lemma isPosSymmetrizable_transpose_iff [Finite ι] [CommSemiring R] [IsDomain R] [PartialOrder R]
    [IsStrictOrderedRing R] :
    Mᵀ.IsPosSymmetrizable ↔ M.IsPosSymmetrizable :=
  ⟨transpose_transpose M ▸ .transpose, .transpose⟩

lemma IsPosSymmetrizable.submatrix [Semiring R] [Preorder R] (f : κ → ι)
    (h : M.IsPosSymmetrizable) : (M.submatrix f f).IsPosSymmetrizable := by
  obtain ⟨d, hd, h⟩ := h
  use d ∘ f
  simp [hd, h]

lemma isPosSymmetrizable_iff_of_pairwise_eq [Semiring R] [LT R]
    (h : Pairwise fun i j ↦ M i j = N i j) : M.IsPosSymmetrizable ↔ N.IsPosSymmetrizable := by
  refine ⟨fun ⟨d, hd, hM⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩, fun ⟨d, hd, hM⟩ ↦ ⟨d, hd, fun i j ↦ ?_⟩⟩
  · by_cases! hij : i = j
    · rw [hij]
    · rw [← h hij, hM, h hij.symm]
  · by_cases! hij : i = j
    · rw [hij]
    · rw [h hij, hM, h hij.symm]

@[simp]
lemma isPosSymmetrizable_iff_add_diagonal [DecidableEq ι] [Semiring R] [LT R] (d : ι → R) :
    (M + diagonal d).IsPosSymmetrizable ↔ M.IsPosSymmetrizable := by
  rw [isPosSymmetrizable_iff_of_pairwise_eq]
  intro _ _ h
  simp [h]

/-- Extends positive symmetry from the complement of an index `v` to the full matrix,
given a positive symmetry condition on the entries with `v`. -/
lemma IsPosSymmetrizable.mk_of_forall_ne {k : ι} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] (e : ι → R) (he : ∀ i, 0 < e i)
    (hE : ∀ i ≠ k, ∀ j ≠ k, e i * M i j = e j * M j i)
    (h : ∃ a > 0, ∃ b > 0, ∀ j ≠ k, b * M k j = a * e j * M j k) :
    M.IsPosSymmetrizable := by
  classical
  obtain ⟨a, ha, b, hb, h⟩ := h
  use fun i ↦ if i = k then b else a * e i
  refine ⟨fun i ↦ ?_, fun i j ↦ ?_⟩
  · by_cases hi : i = k
    · simp [hi, hb]
    · simp [hi, mul_pos ha (he i)]
  · by_cases hi : i = k <;> by_cases hj : j = k <;> grind

end IsPosSymmetrizable

end Matrix
