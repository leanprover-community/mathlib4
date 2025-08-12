/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# Eigenvalues, Eigenvectors and Spectrum for Matrices

This file collects results about eigenvectors, eigenvalues and spectrum specific to matrices
over a nontrivial commutative ring, nontrivial commutative ring without zero divisors, or field.

## Tags
eigenspace, eigenvector, eigenvalue, spectrum, matrix

-/

section SpectrumDiagonal

variable {R n M : Type*} [DecidableEq n] [Fintype n]

open Matrix Module End

section NontrivialCommRing

variable [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]

/-- Basis vectors are eigenvectors of associated diagonal linear operator. -/
lemma hasEigenvector_toLin_diagonal (d : n → R) (i : n) (b : Basis n R M) :
    HasEigenvector (toLin b b (diagonal d)) (d i) (b i) :=
  ⟨mem_eigenspace_iff.mpr <| by simp [diagonal], Basis.ne_zero b i⟩

/-- Standard basis vectors are eigenvectors of any associated diagonal linear operator. -/
lemma hasEigenvector_toLin'_diagonal (d : n → R) (i : n) :
    HasEigenvector (toLin' (diagonal d)) (d i) (Pi.basisFun R n i)  :=
  hasEigenvector_toLin_diagonal _ _ (Pi.basisFun R n)

/-- Eigenvalues of a diagonal linear operator are the diagonal entries. -/
lemma hasEigenvalue_toLin_diagonal_iff (d : n → R) {μ : R} [NoZeroSMulDivisors R M]
    (b : Basis n R M) : HasEigenvalue (toLin b b (diagonal d)) μ ↔ ∃ i, d i = μ := by
  have (i : n) : HasEigenvalue (toLin b b (diagonal d)) (d i) :=
    hasEigenvalue_of_hasEigenvector <| hasEigenvector_toLin_diagonal d i b
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
      exact (hasEigenvector_toLin_diagonal d i b).apply_eq_smul
    have hμ_notMem : μ ∉ Set.range d := by simpa using fun i ↦ (hμ i)
    have := eigenspaces_iSupIndep (toLin b b (diagonal d)) |>.disjoint_biSup hμ_notMem
    rw [h_iSup, disjoint_top] at this
    exact h_eig this
  · rintro ⟨i, rfl⟩
    exact this i

/-- Eigenvalues of a diagonal linear operator with respect to standard basis
are the diagonal entries. -/
lemma hasEigenvalue_toLin'_diagonal_iff [NoZeroDivisors R] (d : n → R) {μ : R} :
    HasEigenvalue (toLin' (diagonal d)) μ ↔ (∃ i, d i = μ) :=
  hasEigenvalue_toLin_diagonal_iff _ <| Pi.basisFun R n

end NontrivialCommRing

namespace Matrix

variable [CommRing R] [AddCommGroup M] [Module R M] (d : n → R) {μ : R} (b : Basis n R M)

@[simp]
lemma iSup_eigenspace_toLin_diagonal_eq_top :
    ⨆ μ, eigenspace ((diagonal d).toLin b b) μ = ⊤ := by
  refine (Submodule.eq_top_iff_forall_basis_mem b).mpr fun j ↦ ?_
  exact Submodule.mem_iSup_of_mem (d j) <| by simp [diagonal_apply]

@[simp]
lemma iSup_eigenspace_toLin'_diagonal_eq_top :
    ⨆ μ, eigenspace (diagonal d).toLin' μ = ⊤ :=
  iSup_eigenspace_toLin_diagonal_eq_top d <| Pi.basisFun R n

variable [IsDomain R]

@[simp]
lemma maxGenEigenspace_toLin_diagonal_eq_eigenspace :
    maxGenEigenspace ((diagonal d).toLin b b) μ = eigenspace ((diagonal d).toLin b b) μ := by
  refine le_antisymm (fun x hx ↦ ?_) eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace _ _ _).mp hx
  replace hk (j : n) : b.repr x j = 0 ∨ d j = μ ∧ k ≠ 0 := by
    have aux : (diagonal d).toLin b b - μ • 1 = (diagonal (d - μ • 1)).toLin b b := by
      change _ = (diagonal fun i ↦ d i - _).toLin b b; rw [← diagonal_sub]; simp [one_eq_id]
    rw [aux, ← toLin_pow, diagonal_pow, toLin_apply_eq_zero_iff] at hk
    simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero] using hk j
  have aux (j : n) : (b.repr x j * d j) • b j = μ • (b.repr x j • b j) := by
    rcases hk j with hj | hj
    · simp [hj]
    · rw [← hj.1, mul_comm, MulAction.mul_smul]
  simp [toLin_apply, mulVec_eq_sum, diagonal_apply, aux, ← Finset.smul_sum]

@[simp]
lemma maxGenEigenspace_toLin'_diagonal_eq_eigenspace :
    maxGenEigenspace (diagonal d).toLin' μ = eigenspace (diagonal d).toLin' μ :=
  maxGenEigenspace_toLin_diagonal_eq_eigenspace d <| Pi.basisFun R n

end Matrix

/-- The spectrum of the diagonal operator is the range of the diagonal viewed as a function. -/
@[simp] lemma spectrum_diagonal [Field R] (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n), ← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
