/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Order.T5

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

@[expose] public section

open Topology Unitary

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

variable (hA : IsHermitian A)

/-- The star algebra homomorphism underlying the instance of the continuous functional
calculus of a Hermitian matrix. This is an auxiliary definition and is not intended
for use outside of this file. -/
@[simps]
noncomputable def cfcAux : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (Matrix n n 𝕜) where
  toFun g := conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary <|
    diagonal (RCLike.ofReal ∘ g ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    simp only [ContinuousMap.coe_mul, ← map_mul, diagonal_mul_diagonal, Function.comp_apply]
    rfl
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← map_add, diagonal_add, Function.comp_apply]
    rfl
  commutes' r := by
    simp only [Function.comp_def, algebraMap_apply, smul_eq_mul, mul_one]
    rw [← mul_one (algebraMap _ _ _), ← coe_mul_star_self hA.eigenvectorUnitary,
      ← Algebra.left_comm, coe_star, ← mul_assoc, conjStarAlgAut_apply]
    rfl
  map_star' f := by
    simp only [star_trivial, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose, Pi.star_def,
      Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rfl

lemma isClosedEmbedding_cfcAux : IsClosedEmbedding hA.cfcAux := by
  have h0 : FiniteDimensional ℝ C(spectrum ℝ A, ℝ) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ) (E := C(spectrum ℝ A, ℝ))
    (F := Matrix n n 𝕜) (f := hA.cfcAux) <| LinearMap.ker_eq_bot'.mpr fun f hf ↦ ?_
  have h2 :
      diagonal (RCLike.ofReal ∘ f ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
        = (0 : Matrix n n 𝕜) := by
    simp only [LinearMap.coe_coe, cfcAux_apply, conjStarAlgAut_apply] at hf
    replace hf := congr($hf * (hA.eigenvectorUnitary : Matrix n n 𝕜))
    simp only [mul_assoc, SetLike.coe_mem, Unitary.star_mul_self_of_mem, mul_one, zero_mul] at hf
    simpa [← mul_assoc] using congr((star hA.eigenvectorUnitary : Matrix n n 𝕜) * $hf)
  ext x
  simp only [ContinuousMap.zero_apply]
  obtain ⟨x, hx⟩ := x
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [← diagonal_zero] at h2
  have := diagonal_eq_diagonal_iff.mp h2
  exact RCLike.ofReal_eq_zero.mp (this i)

lemma cfcAux_id : hA.cfcAux (.restrict (spectrum ℝ A) (.id ℝ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

/-- Instance of the continuous functional calculus for a Hermitian matrix over `𝕜` with
`RCLike 𝕜`. -/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  exists_cfc_of_predicate a ha := by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f ↦ ?map_spec,
      fun f ↦ ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [cfcAux_apply, conjStarAlgAut_apply, Unitary.spectrum_star_right_conjugate]
        rintro - ⟨x, rfl⟩
        apply spectrum.of_algebraMap_mem 𝕜
        simp only [Function.comp_apply, Set.mem_range, spectrum_diagonal]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.spectrum_real_eq_range_eigenvalues ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      simp only [isSelfAdjoint_iff, cfcAux_apply, ← map_star]
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      congr!
      simp [Pi.star_def, Function.comp_def]
  spectrum_nonempty a ha := by
    obtain (h | h) := isEmpty_or_nonempty n
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix n n 𝕜)
      exact False.elim <| Matrix.of.symm.injective.ne hxy <| Subsingleton.elim _ _
    · exact spectrum_real_eq_range_eigenvalues ha ▸ Set.range_nonempty _
  predicate_zero := .zero _

/-- The continuous functional calculus of a Hermitian matrix as a triple product using the
spectral theorem. Note that this actually operates on bare functions since every function is
continuous on the spectrum of a matrix, since the spectrum is finite. This is shown to be equal to
the generic continuous functional calculus API in `Matrix.IsHermitian.cfc_eq`. In general, users
should prefer the generic API, especially because it will make rewriting easier. -/
protected noncomputable def cfc (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))

lemma cfcHom_eq_cfcAux : cfcHom hA.isSelfAdjoint = hA.cfcAux :=
  cfcHom_eq_of_continuous_of_map_id hA hA.cfcAux
    hA.isClosedEmbedding_cfcAux.continuous hA.cfcAux_id

instance instContinuousFunctionalCalculusIsClosedEmbedding :
    ClosedEmbeddingContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  isClosedEmbedding _ hA := cfcHom_eq_cfcAux hA ▸ hA.isHermitian.isClosedEmbedding_cfcAux

lemma cfc_eq (f : ℝ → ℝ) : cfc f A = hA.cfc f := by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_restrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function.comp_def, Set.restrict_apply,
    IsHermitian.cfc]

open Polynomial in
lemma charpoly_cfc_eq (f : ℝ → ℝ) :
    (cfc f A).charpoly = ∏ i, (X - C (f (hA.eigenvalues i) : 𝕜)) := by
  rw [cfc_eq hA f, IsHermitian.cfc, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

end IsHermitian
end Matrix
