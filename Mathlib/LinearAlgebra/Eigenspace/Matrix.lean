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

variable [CommRing R] [IsDomain R] {d : n → R}

@[simp]
lemma maxGenEigenspace_diagonal_eq_bot_iff {μ : R} :
    maxGenEigenspace (diagonal d).toLin' μ = ⊥ ↔ μ ∉ Set.range d := by
  rw [← not_iff_not]
  simp only [Set.mem_range, not_exists, not_forall, not_not, ← ne_eq, Submodule.ne_bot_iff]
  refine ⟨fun ⟨x, hx, hx₀⟩ ↦ ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx₀
    use i
    have : (diagonal d).toLin' - μ • 1 = (diagonal (d - μ • 1)).toLin' := by
      aesop (add simp Pi.single_apply)
    obtain ⟨k, hk⟩ : ∃ k, diagonal ((d - μ • 1) ^ k) *ᵥ x = 0 := by
      simpa only [mem_maxGenEigenspace, this, ← toLin'_pow, toLin'_apply, diagonal_pow] using hx
    replace hk : x i * (d i - μ) ^ k = 0 := by
      simpa [mulVec_eq_sum, diagonal_apply] using congr_fun hk i
    simp only [mul_eq_zero, hi, pow_eq_zero_iff', ne_eq, false_or, sub_eq_zero] at hk
    exact hk.1
  · rintro ⟨i, rfl⟩
    refine ⟨Pi.single i 1, (mem_maxGenEigenspace _ _ _).mpr ⟨1, ?_⟩, by simp⟩
    ext j
    simp [Pi.single_apply]

@[simp]
lemma iSup_maxGenEigenspace_diagonal_eq_top :
    ⨆ μ, maxGenEigenspace (diagonal d).toLin' μ = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun v ↦ ?_
  suffices ⨆ μ, maxGenEigenspace (Matrix.diagonal d).toLin' μ =
      ⨆ i ∈ Finset.univ, maxGenEigenspace (Matrix.diagonal d).toLin' (d i) by
    rw [this, Submodule.mem_iSup_finset_iff_exists_sum]
    let μ (i : n) : maxGenEigenspace (diagonal d).toLin' (d i) := ⟨Pi.single i (v i),
      (mem_maxGenEigenspace _ _ _).mpr ⟨1, by ext j; simp [Pi.single_apply, mul_comm (v i)]⟩⟩
    exact ⟨μ, Finset.univ_sum_single v⟩
  let p (μ : R) : Prop := maxGenEigenspace (diagonal d).toLin' μ = ⊥
  have hp_neg (μ : R) : ¬ p μ ↔ μ ∈ Set.range d := by simp [p]
  have hp_pos (μ : R) (hμ : p μ) : maxGenEigenspace (diagonal d).toLin' μ = ⊥ := hμ
  simp only [Finset.mem_univ, iSup_pos]
  rw [iSup_split _ p]
  simp only [biSup_congr hp_pos, hp_neg, iSup_bot, bot_sup_eq, iSup_range]

end Matrix

/-- The spectrum of the diagonal operator is the range of the diagonal viewed as a function. -/
lemma spectrum_diagonal [Field R] (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (toLinAlgEquiv <| Pi.basisFun R n), ← hasEigenvalue_iff_mem_spectrum]
  exact hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
