/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Eigenvalues, Eigenvectors and Spectrum for Matrices

This file collects results about eigenvectors, eigenvalues and spectrum specific to matrices.

## Tags
eigenspace, eigenvector, eigenvalue, eigen, spectrum, matrices, matrix

-/

section SpectrumDiagonal

variable {R : Type*} [Field R] {n : Type*} [DecidableEq n][Fintype n]

open Matrix
open Module.End

/--  Standard basis vectors are eigenvectors of any associated diagonal linear operator. -/
lemma hasEigenvector_toLin'_diagonal (d : n → R) (i : n) :
    Module.End.HasEigenvector (toLin' (diagonal d)) (d i) (Pi.basisFun R n i) := by
  constructor
  · rw [mem_eigenspace_iff]
    ext j
    simp only [diagonal, Pi.basisFun_apply, toLin'_apply, mulVec_stdBasis_apply, transpose_apply,
      of_apply, Pi.smul_apply, LinearMap.stdBasis_apply', smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs
    all_goals simp_all
  · rw [Function.ne_iff]; simp

/-- Eigenvalues of a diagonal linear operator are the diagonal entries. -/
lemma hasEigenvalue_toLin'_diagonal_iff (d : n → R) {μ : R} :
    HasEigenvalue (toLin' (diagonal d)) μ ↔ ∃ i, d i = μ := by
  have (i : n) : HasEigenvalue (toLin' (diagonal d)) (d i) := by
    exact hasEigenvalue_of_hasEigenvector <| hasEigenvector_toLin'_diagonal d i
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ ∈ Set.range d, eigenspace (toLin' (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun R n).span_eq, Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin'_diagonal d i).apply_eq_smul
    have hμ_not_mem : μ ∉ Set.range d := by simpa using fun i ↦ (hμ i)
    have := eigenspaces_independent (toLin' (diagonal d)) |>.disjoint_biSup hμ_not_mem
    rw [h_iSup, disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

/-- The spectrum of the diagonal operator is the range of the diagonal viewed as a function. -/
lemma spectrum_diagonal (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n),
    ← hasEigenvalue_iff_mem_spectrum, Set.mem_range]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
