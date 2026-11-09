/-
Copyright (c) 2026 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/

module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetrizable Matrices

A matrix `M` is symmetrizable if there exists a diagonal matrix `D` such that `D * M` is symmetric.
If furthermore the diagonal entries of `D` are positive, `M` is said to be positively
symmetrizable.

-/

@[expose] public section

namespace Matrix

variable {ι R : Type*} {M : Matrix ι ι R}

def IsSymmetrizable [Zero R] [Mul R] (M : Matrix ι ι R) : Prop :=
  ∃ d : ι → R, (∀ i, d i ∈ nonZeroDivisors R) ∧ ∀ i j, d i * M i j = d j * M j i

section IsSymmetrizable

lemma IsSymm.IsSymmetrizable [NonAssocRing R] [Nontrivial R] (h : M.IsSymm) :
    M.IsSymmetrizable := by
  use 1
  simp [h.apply]

lemma isSymmetrizable_iff [DecidableEq ι] [Fintype ι] [NonUnitalNonAssocSemiring R] :
    M.IsSymmetrizable ↔ ∃ d : ι → R, (∀ i, d i ≠ 0) ∧ ((diagonal d) * M).IsSymm := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨d, hd, h⟩ := h
    use d, hd
    ext i j
    rw [diagonal_mul, transpose_apply, diagonal_mul, h i j]
  · obtain ⟨d, hd, h⟩ := h
    use d, hd
    intro i j
    rw [← diagonal_mul, ← diagonal_mul, h.apply i j]

lemma transpose_isSymmetrizable [Finite ι] [CommSemiring R] [IsDomain R] (h : M.IsSymmetrizable) :
    Mᵀ.IsSymmetrizable := by
  classical
  have := Fintype.ofFinite
  obtain ⟨d, hd, h⟩ := h
  use fun i ↦ ∏ k ∈ Finset.univ.erase i, d k
  refine ⟨fun _ ↦ Finset.prod_ne_zero_iff.mpr fun a _ ↦ hd a, ?_⟩
  intro i j
  simp_rw [transpose_apply]
  by_cases! hij : i = j
  · rw [hij]
  have hi := Finset.prod_erase_mul (Finset.univ.erase j) d
    <| Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have hj := Finset.prod_erase_mul (Finset.univ.erase i) d
    <| Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← hj, mul_assoc, h j i, ← mul_assoc, ← hi, Finset.erase_comm]

lemma transpose_isSymmetrizable_iff [Finite ι] [CommSemiring R] [IsDomain R] :
    Mᵀ.IsSymmetrizable ↔ M.IsSymmetrizable :=
  ⟨transpose_transpose M ▸ transpose_isSymmetrizable, transpose_isSymmetrizable⟩

end IsSymmetrizable

def IsPosSymmetrizable [Zero R] [LT R] [Mul R] (M : Matrix ι ι R) : Prop :=
  ∃ d : ι → R, (∀ i, 0 < d i) ∧ ∀ i j, d i * M i j = d j * M j i

section IsPosSymmetrizable

lemma IsPosSymmetrizable.isSymmetrizable [Zero R] [Mul R] [Preorder R]
    (hM : M.IsPosSymmetrizable) : M.IsSymmetrizable := by
  obtain ⟨d, hd, h⟩ := hM
  exact ⟨d, fun i ↦ (hd i).ne.symm, h⟩

lemma isPosSymmetrizable_iff [DecidableEq ι] [Fintype ι] [LT R] [NonUnitalNonAssocSemiring R] :
    M.IsPosSymmetrizable ↔ ∃ d : ι → R, (∀ i, 0 < d i) ∧ ((diagonal d) * M).IsSymm := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨d, hd, h⟩ := h
    use d, hd
    ext i j
    rw [diagonal_mul, transpose_apply, diagonal_mul, h i j]
  · obtain ⟨d, hd, h⟩ := h
    use d, hd
    intro i j
    rw [← diagonal_mul, ← diagonal_mul, h.apply i j]

lemma transpose_isPosSymmetrizable [Finite ι] [CommSemiring R] [IsDomain R] [PartialOrder R]
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
  rw [← hj, mul_assoc, h j i, ← mul_assoc, ← hi, Finset.erase_comm]

lemma transpose_isPosSymmetrizable_iff [Finite ι] [CommSemiring R] [IsDomain R] [PartialOrder R]
    [ZeroLEOneClass R] [PosMulStrictMono R] :
    M.IsPosSymmetrizable ↔ Mᵀ.IsPosSymmetrizable :=
  ⟨transpose_transpose M ▸ transpose_isPosSymmetrizable, transpose_isPosSymmetrizable⟩

end IsPosSymmetrizable

end Matrix
