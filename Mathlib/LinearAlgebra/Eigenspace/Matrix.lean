/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Eigenvalues, Eigenvectors and Spectrum for Matrices

This file collects results about eigenvectors, eigenvalues and spectrum specific to matrices
over a field.

## Tags
eigenspace, eigenvector, eigenvalue, eigen, spectrum, matrices, matrix

-/

section SpectrumDiagonal

variable {R : Type*} [Field R] {n : Type*} [DecidableEq n] [Fintype n] (M : Type*)
  [AddCommGroup M] [Module R M]

open Matrix
open Module.End

/-- Basis vectors are eigenvectors of associated diagonal linear operator. -/
lemma hasEigenvector_toLin_diagonal (d : n → R) (i : n) (b : Basis n R M) :
    Module.End.HasEigenvector (toLin b b (diagonal d)) (d i) (b i) :=
  ⟨mem_eigenspace_iff.mpr <| by simp [diagonal], Basis.ne_zero b i⟩

/--  Standard basis vectors are eigenvectors of any associated diagonal linear operator. -/
lemma hasEigenvector_toLin'_diagonal (d : n → R) (i : n) :
    Module.End.HasEigenvector (toLin' (diagonal d)) (d i) (Pi.basisFun R n i) :=
  hasEigenvector_toLin_diagonal (d : n → R) (i : n) (b := Pi.basisFun R n)

/-- Eigenvalues of a diagonal linear operator are the diagonal entries. -/
lemma hasEigenvalue_toLin_diagonal_iff (d : n → R) {μ : R} (b : Basis n R M) :
    HasEigenvalue (toLin b b (diagonal d)) μ ↔ ∃ i, d i = μ := by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) := by
    exact hasEigenvalue_of_hasEigenvector <| hasEigenvector_toLin_diagonal _ d i b
  constructor
  · contrapose!
    intro hμ h_eig
    have h_iSup : ⨆ μ ∈ Set.range d, eigenspace (toLin b b (diagonal d)) μ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro - ⟨i, rfl⟩
      simp only [SetLike.mem_coe]
      apply Submodule.mem_iSup_of_mem (d i)
      apply Submodule.mem_iSup_of_mem ⟨i, rfl⟩
      rw [mem_eigenspace_iff]
      exact (hasEigenvector_toLin_diagonal _ d i b).apply_eq_smul
    have hμ_not_mem : μ ∉ Set.range d := by simpa using fun i ↦ (hμ i)
    have := eigenspaces_independent (toLin b b (diagonal d)) |>.disjoint_biSup hμ_not_mem
    rw [h_iSup, disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

/-- Eigenvalues of a diagonal linear operator with respect to standard basis
    are the diagonal entries. -/
lemma hasEigenvalue_toLin'_diagonal_iff (d : n → R) {μ : R} :
    HasEigenvalue (toLin' (diagonal d)) μ ↔ ∃ i, d i = μ := by
  exact hasEigenvalue_toLin_diagonal_iff (n → R) d (Pi.basisFun R n)

/-- The spectrum of the diagonal operator is the range of the diagonal viewed as a function. -/
lemma spectrum_diagonal (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n),
    ← hasEigenvalue_iff_mem_spectrum, Set.mem_range]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
