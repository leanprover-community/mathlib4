/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Topology.ContinuousMap.Units

/-!
# Continuous Functional Calculus for Hermitian Matrices

This file defines an instance of the continuous functional calculus for Hermitian matrices over an
`RCLike` field `𝕜`.

## Main Results

- `Matrix.IsHermitian.cfc` : Realization of the functional calculus for a Hermitian matrix
  as the triple product `U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U` with
  `U = eigenvectorUnitary hA`.

- `cfc_eq` : Proof that the above agrees with the continuous functional calculus.

- `Matrix.IsHermitian.instContinuousFunctionalCalculus` : Instance of the continuous functional
  calculus for a Hermitian matrix `A` over `𝕜`.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

open Topology

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

lemma finite_real_spectrum : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective ℝ 𝕜).injOn

instance : Finite (spectrum ℝ A) := A.finite_real_spectrum

namespace IsHermitian

variable (hA : IsHermitian A)

/-- The `ℝ`-spectrum of a Hermitian matrix over `RCLike` field is the range of the eigenvalue
function -/
theorem eigenvalues_eq_spectrum_real {a : Matrix n n 𝕜} (ha : IsHermitian a) :
    spectrum ℝ a = Set.range (ha.eigenvalues) := by
  ext x
  conv_lhs => rw [ha.spectral_theorem, unitary.spectrum.unitary_conjugate,
  ← spectrum.algebraMap_mem_iff 𝕜, spectrum_diagonal, RCLike.algebraMap_eq_ofReal]
  simp

/-- The star algebra homomorphism underlying the instance of the continuous functional
calculus of a Hermitian matrix. This is an auxiliary definition and is not intended
for use outside of this file. -/
@[simps]
noncomputable def cfcAux : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (Matrix n n 𝕜) where
  toFun := fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) *
    diagonal (RCLike.ofReal ∘ g ∘ (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩))
    * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    have {a b c d e f : Matrix n n 𝕜} : (a * b * c) * (d * e * f) = a * (b * (c * d) * e) * f := by
      simp only [mul_assoc]
    simp only [this, ContinuousMap.coe_mul, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one,
      diagonal_mul_diagonal, Function.comp_apply]
    congr! with i
    simp
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← add_mul, ← mul_add, diagonal_add, Function.comp_apply]
    congr! with i
    simp
  commutes' r := by
    simp only [Function.comp_def, algebraMap_apply, smul_eq_mul, mul_one]
    rw [← mul_one (algebraMap _ _ _), ← unitary.coe_mul_star_self hA.eigenvectorUnitary,
      ← Algebra.left_comm, unitary.coe_star, mul_assoc]
    congr!
  map_star' f := by
    simp only [star_trivial, StarMul.star_mul, star_star, star_eq_conjTranspose (diagonal _),
      diagonal_conjTranspose, mul_assoc]
    congr!
    ext
    simp

lemma isClosedEmbedding_cfcAux : IsClosedEmbedding hA.cfcAux := by
  have h0 : FiniteDimensional ℝ C(spectrum ℝ A, ℝ) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ) (E := C(spectrum ℝ A, ℝ))
    (F := Matrix n n 𝕜) (f := hA.cfcAux) <| LinearMap.ker_eq_bot'.mpr fun f hf ↦ ?_
  have h2 :
      diagonal (RCLike.ofReal ∘ f ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
        = (0 : Matrix n n 𝕜) := by
    simp only [LinearMap.coe_coe, cfcAux_apply] at hf
    replace hf := congr($(hf) * (eigenvectorUnitary hA : Matrix n n 𝕜))
    simp only [mul_assoc, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one, zero_mul] at hf
    simpa [← mul_assoc] using congr((star hA.eigenvectorUnitary : Matrix n n 𝕜) * $(hf))
  ext x
  simp only [ContinuousMap.zero_apply]
  obtain ⟨x, hx⟩ := x
  obtain ⟨i, rfl⟩ := hA.eigenvalues_eq_spectrum_real ▸ hx
  rw [← diagonal_zero] at h2
  have := (diagonal_eq_diagonal_iff).mp h2
  refine RCLike.ofReal_eq_zero.mp (this i)

lemma cfcAux_id : hA.cfcAux (.restrict (spectrum ℝ A) (.id ℝ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  congr!

/-- Instance of the continuous functional calculus for a Hermitian matrix over `𝕜` with
`RCLike 𝕜`. -/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  exists_cfc_of_predicate a ha := by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux, ha.cfcAux_id, fun f ↦ ?map_spec,
      fun f ↦ ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [cfcAux_apply, unitary.spectrum.unitary_conjugate]
        rintro - ⟨x , rfl⟩
        apply spectrum.of_algebraMap_mem 𝕜
        simp only [Function.comp_apply, Set.mem_range, spectrum_diagonal]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.eigenvalues_eq_spectrum_real ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      simp only [isSelfAdjoint_iff, cfcAux_apply, mul_assoc, star_mul, star_star]
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      congr!
      simp [Pi.star_def, Function.comp_def]
  spectrum_nonempty a ha := by
    obtain (h | h) := isEmpty_or_nonempty n
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix n n 𝕜)
      exact False.elim <| Matrix.of.symm.injective.ne hxy <| Subsingleton.elim _ _
    · exact eigenvalues_eq_spectrum_real ha ▸ Set.range_nonempty _
  predicate_zero := .zero _

/-- The continuous functional calculus of a Hermitian matrix as a triple product using the
spectral theorem. Note that this actually operates on bare functions since every function is
continuous on the spectrum of a matrix, since the spectrum is finite. This is shown to be equal to
the generic continuous functional calculus API in `Matrix.IsHermitian.cfc_eq`. In general, users
should prefer the generic API, especially because it will make rewriting easier. -/
protected noncomputable def cfc (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
    * star (eigenvectorUnitary hA : Matrix n n 𝕜)

lemma cfc_eq (f : ℝ → ℝ) : cfc f A = hA.cfc f := by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_restrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function.comp_def, Set.restrict_apply,
    IsHermitian.cfc]

end IsHermitian
end Matrix
