/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Topology.ContinuousFunction.UniqueCFC
import Mathlib.Analysis.NormedSpace.Star.Matrix

/-!
# Continuous Functional Calculus for Hermitian Matrices

This file defines an instance of the continuous functional calculus for Hermitian matrices over an
RCLike field 𝕜.

## Main Results

- definition of φ : the real StarAlgHom from C(spectrum ℝ A, ℝ) to (Matrix n n 𝕜) appearing in the
                    instance.
- instContinuousFunctionalCalculus : Instance of the Continuous functional Calculus for a hermitian
                                     matrix A over 𝕜.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

section ConjugateUnits

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Conjugation by a unit preserves the spectrum, inverse on right. -/
@[simp]
lemma spectrum.conjugate_units {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices ∀ (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) ⊆ spectrum R b by
    refine le_antisymm (this a u) ?_
    apply le_of_eq_of_le ?_ <| this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose! hμ
  simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ |>.mul u⁻¹.isUnit

/-- Conjugation by a unit preserves the spectrum, inverse on left. -/
@[simp]
lemma spectrum.conjugate_units' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by
  simpa using spectrum.conjugate_units (u := u⁻¹)

end ConjugateUnits

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
lemma spectrum.unitary_conjugate {a : A} {u : unitary A} :
    spectrum R (u * a * (star u : A)) = spectrum R a :=
  spectrum.conjugate_units (u := unitary.toUnits u)

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
lemma spectrum.unitary_conjugate' {a : A} {u : unitary A} :
    spectrum R ((star u : A) * a * u) = spectrum R a := by
  simpa using spectrum.unitary_conjugate (u := star u)

end UnitaryConjugate

section FiniteSpectrum

universe u v w

/-- An endomorphism of a finite-dimensional vector space has a finite spectrum. -/
theorem Module.End.finite_spectrum {K : Type v} {V : Type w} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) :
    Set.Finite (spectrum K f) := by
  convert f.finite_hasEigenvalue
  ext f x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

variable {n R : Type*} [Field R] [Fintype n] [DecidableEq n]

/-- An n x n matrix over a ring has a finite spectrum. -/
theorem Matrix.finite_spectrum (A : Matrix n n R) : Set.Finite (spectrum R A) := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _

instance Matrix.instFiniteSpectrum (A : Matrix n n R) : Finite (spectrum R A) :=
  Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

end FiniteSpectrum

section SpectrumDiagonal

variable {R : Type*} [Field R] {n : Type*} [DecidableEq n][Fintype n]

open Module.End

/--  Standard basis vectors are eigenvectors of any associated diagonal linear operator. -/
lemma Matrix.hasEigenvector_toLin'_diagonal (d : n → R) (i : n) :
    Module.End.HasEigenvector (Matrix.toLin' (diagonal d)) (d i) (Pi.basisFun R n i) := by
  constructor
  · rw [mem_eigenspace_iff]
    ext j
    simp only [diagonal, Pi.basisFun_apply, toLin'_apply, mulVec_stdBasis_apply, transpose_apply,
      of_apply, Pi.smul_apply, LinearMap.stdBasis_apply', smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs
    all_goals simp_all
  · rw [Function.ne_iff]; simp

/-- Eigenvalues of a diagonal linear operator are the diagonal entries. -/
lemma Matrix.hasEigenvalue_toLin'_diagonal_iff (d : n → R) {μ : R} :
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
lemma Matrix.spectrum_diagonal (d : n → R) :
    spectrum R (diagonal d) = Set.range d := by
  ext μ
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n),
    ← hasEigenvalue_iff_mem_spectrum, Set.mem_range]
  exact Matrix.hasEigenvalue_toLin'_diagonal_iff d

end SpectrumDiagonal
namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

namespace IsHermitian

variable [DecidableEq n]

variable {A : Matrix n n 𝕜} (hA : IsHermitian A)

/--Eigenvalues of a Hermitian Matrix, coerced, belong to the spectrum of the assoc.toEuclideanLin -/
theorem eigenvalue_mem_toEuclideanLin_spectrum_RCLike (i : n) :
    (RCLike.ofReal ∘ hA.eigenvalues) i ∈ spectrum 𝕜 (toEuclideanLin A) :=
  LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

/-- Algebra equivalence between the linear maps and continuous linear maps on a finite-dim module.-/
def AlgEquivFiniteDimNormedLinearCLM.{v} (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E][FiniteDimensional 𝕜 E] :
    AlgEquiv (R := 𝕜) (A := E →ₗ[𝕜] E) (B := E →L[𝕜] E) :=
    {LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl}

/--Spectrum of a Hermitian matrix equals the spectrum as a EuclideanLin. -/
theorem spec_toEuclideanLin_eq_spec : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq ((AlgEquiv.trans ((toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜]
  EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) : Matrix n n 𝕜 ≃ₐ[𝕜]
  EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))
  (AlgEquivFiniteDimNormedLinearCLM (EuclideanSpace 𝕜 n)).symm) _

/--Eigenvalues of a hermitian matrix A are in the ℝ spectrum of A. -/
theorem eigenvalue_mem_real : ∀ (i : n), (hA.eigenvalues) i ∈ spectrum ℝ A := by
  intro i
  apply spectrum.of_algebraMap_mem (S := 𝕜) (R := ℝ) (A := Matrix n n 𝕜)
  rw [← spec_toEuclideanLin_eq_spec]
  apply hA.eigenvalue_mem_toEuclideanLin_spectrum_RCLike i

/--Definition of the StarAlgHom for the continuous functional calculus of a Hermitian matrix. -/
@[simps]
noncomputable def φ : StarAlgHom ℝ C(spectrum ℝ A, ℝ) (Matrix n n 𝕜) where
  toFun := fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) *
    diagonal (RCLike.ofReal ∘ g ∘ (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩))
    * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_one' := by simp [Pi.one_def (f := fun _ : n ↦ 𝕜)]
  map_mul' f g := by
    have {a b c d e f : Matrix n n 𝕜} : (a * b * c) * (d * e * f) = a * (b * (c * d) * e) * f := by
      simp only [mul_assoc]
    simp only [this, ContinuousMap.coe_mul, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one,
      diagonal_mul_diagonal, Function.comp_apply]
    congr! with i
    simp
  map_zero' := by simp [Pi.zero_def (f := fun _ : n ↦ 𝕜)]
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← add_mul, ← mul_add, diagonal_add, Function.comp_apply]
    congr! with i
    simp
  commutes' r := by
    simp only [Function.comp, algebraMap_apply, smul_eq_mul, mul_one]
    rw [IsScalarTower.algebraMap_apply ℝ 𝕜 _ r, RCLike.algebraMap_eq_ofReal,
      ← mul_one (algebraMap _ _ _), ← unitary.coe_mul_star_self hA.eigenvectorUnitary,
      ← Algebra.left_comm, unitary.coe_star, mul_assoc]
    congr!
  map_star' f := by
    simp only [star_trivial, StarMul.star_mul, star_star, star_eq_conjTranspose (diagonal _),
      diagonal_conjTranspose, mul_assoc]
    congr!
    ext
    simp

/-- The ℝ-spectrum of a Hermitian Matrix over RCLike field is the range of the eigenvalue function-/
theorem eigenvalues_eq_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian a) :
    (spectrum ℝ a) = Set.range (ha.eigenvalues) := by
  ext x
  conv_lhs => rw [ha.spectral_theorem, spectrum.unitary_conjugate,
  ← spectrum.algebraMap_mem_iff 𝕜, spectrum_diagonal, RCLike.algebraMap_eq_ofReal]
  simp

/--The ℝ-spectrum of an n x n Hermitian matrix is finite. -/
theorem finite_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian a) : (spectrum ℝ a).Finite := by
  have H := Set.finite_range (ha.eigenvalues)
  exact (ha.eigenvalues_eq_spectrum).symm ▸ H

/-- The ℝ-spectrum of an n x n Hermitian matrix over an RCLike field is a compact space. -/
theorem compact_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian a) : CompactSpace (spectrum ℝ a) := by
  convert Finite.compactSpace (X := spectrum ℝ a)
  refine Set.finite_coe_iff.mpr ?_
  apply finite_spectrum
  assumption

/-- Instance of the Continuous Functional Calculus for a Hermitian Matrix over an RCLike field.-/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (IsHermitian : Matrix n n 𝕜 → Prop) where
  exists_cfc_of_predicate a ha := by
    refine ⟨φ ha, ?closedEmbedding, ?mapId, ?map_spec, ?hermitian⟩
    case closedEmbedding =>
      have h0 : FiniteDimensional ℝ C(spectrum ℝ a, ℝ) := by
        have : Finite (spectrum ℝ a) := by refine finite_spectrum ha
        apply FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ))
        exact DFunLike.coe_injective
      have hφ : LinearMap.ker ha.φ = ⊥ := by
        refine LinearMap.ker_eq_bot'.mpr ?_
        intro f hf
        have h2 : diagonal
             (RCLike.ofReal ∘ ⇑f ∘ fun i ↦ ⟨ha.eigenvalues i, ha.eigenvalue_mem_real i⟩)
             = (0 : Matrix n n 𝕜) := by
           rw [φ_apply] at hf
           have hlr : (star ha.eigenvectorUnitary : Matrix n n 𝕜) *
              ((eigenvectorUnitary ha : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ f ∘
                (fun i ↦ ⟨ha.eigenvalues i, ha.eigenvalue_mem_real i⟩)) *
                star (eigenvectorUnitary ha : Matrix n n 𝕜)) *
                (ha.eigenvectorUnitary : Matrix n n 𝕜) =
                (star ha.eigenvectorUnitary : Matrix n n 𝕜) *
                (0 : Matrix n n 𝕜) * (ha.eigenvectorUnitary : Matrix n n 𝕜) := by congr
           simp only [← mul_assoc, SetLike.coe_mem, unitary.star_mul_self_of_mem, one_mul,
                    mul_zero, zero_mul] at hlr
           simp only [mul_assoc, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one] at hlr
           exact hlr
        ext x
        simp only [ContinuousMap.zero_apply]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.eigenvalues_eq_spectrum ▸ hx
        rw [← diagonal_zero] at h2
        have := (diagonal_eq_diagonal_iff).mp h2
        exact RCLike.ofReal_eq_zero.mp (this i)
      have H := ha.compact_spectrum
      apply LinearMap.closedEmbedding_of_injective (𝕜 := ℝ) (E := C(spectrum ℝ a, ℝ))
        (F := Matrix n n 𝕜) (f := ha.φ) hφ
    case mapId =>
      conv_rhs => rw [ha.spectral_theorem]
      congr!
    case map_spec =>
      intro f
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [φ_apply ,spectrum.unitary_conjugate]
        rintro - ⟨x , rfl⟩
        apply spectrum.of_algebraMap_mem (R := ℝ) (S := 𝕜)
        simp only [spectrum_diagonal (R := 𝕜)
            (RCLike.ofReal ∘ f ∘ (fun i ↦ ⟨ha.eigenvalues i, ha.eigenvalue_mem_real i⟩))
            , Function.comp_apply, Set.mem_range]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.eigenvalues_eq_spectrum ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      intro f
      simp only [φ_apply, mul_assoc, IsHermitian, ← star_eq_conjTranspose, star_mul, star_star]
      congr!
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      congr!
      simp only [Pi.star_def, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
      rfl
end IsHermitian
end Matrix
