/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Linear maps between direct sums

This file contains results about linear maps which respect direct sum decompositions of their
domain and codomain.

-/

open Set BigOperators DirectSum

attribute [local instance]
  isNoetherian_of_isNoetherianRing_of_finite
  Module.free_of_finite_type_torsion_free'

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {N : ι → Submodule R M} [DecidableEq ι] (h : IsInternal N)

namespace LinearMap

/-- If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decompositions. -/
lemma toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Fintype (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
    [Fintype ι] (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h₂.collectedBasis_repr_of_mem _ (hf _ (Subtype.mem _)), restrict_apply]
  · simp [hij, h₂.collectedBasis_repr_of_mem_ne _ hij.symm (hf _ (Subtype.mem _))]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

lemma trace_eq_sum_trace_restrict [Fintype ι]
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i, trace R (N i) (f.restrict (hf i)) := by
  let b : (i : ι) → Basis _ R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b),
    toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hf, Matrix.trace_blockDiagonal',
    ← trace_eq_matrix_trace]

lemma trace_eq_sum_trace_restrict' (hN : {i | N i ≠ ⊥}.Finite)
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i in hN.toFinset, trace R (N i) (f.restrict (hf i)) := by
  let _ : Fintype {i // N i ≠ ⊥} := hN.fintype
  let _ : Fintype {i | N i ≠ ⊥} := hN.fintype
  rw [← Finset.sum_coe_sort, trace_eq_sum_trace_restrict (isInternal_ne_bot_iff.mpr h) _]
  exact Fintype.sum_equiv hN.subtypeEquivToFinset _ _ (fun i ↦ rfl)

/-- If `f` and `g` are commuting endomorphisms of a finite, free `R`-module `M`, such that `f`
is triangularizable, then to prove that the trace of `g ∘ f` vanishes, it is sufficient to prove
that the trace of `g` vanishes on each generalized eigenspace of `f`. -/
lemma trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
    {f g : Module.End R M}
    (h_comm : Commute f g)
    (hf : ⨆ μ, ⨆ k, f.generalizedEigenspace μ k = ⊤)
    (hg : ∀ μ, trace R _ (g.restrict (f.mapsTo_iSup_generalizedEigenspace_of_comm h_comm μ)) = 0) :
    trace R _ (g ∘ₗ f) = 0 := by
  have hfg : ∀ μ,
      MapsTo (g ∘ₗ f) ↑(⨆ k, f.generalizedEigenspace μ k) ↑(⨆ k, f.generalizedEigenspace μ k) :=
    fun μ ↦ (f.mapsTo_iSup_generalizedEigenspace_of_comm h_comm μ).comp
      (f.mapsTo_iSup_generalizedEigenspace_of_comm rfl μ)
  suffices ∀ μ, trace R _ ((g ∘ₗ f).restrict (hfg μ)) = 0 by
    classical
    have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
      f.independent_generalizedEigenspace hf
    have h_fin : {μ | ⨆ k, f.generalizedEigenspace μ k ≠ ⊥}.Finite :=
      CompleteLattice.WellFounded.finite_ne_bot_of_independent
        (isNoetherian_iff_wellFounded.mp inferInstance) f.independent_generalizedEigenspace
    simp [trace_eq_sum_trace_restrict' hds h_fin hfg, this]
  intro μ
  replace h_comm : Commute (g.restrict (f.mapsTo_iSup_generalizedEigenspace_of_comm h_comm μ))
      (f.restrict (f.mapsTo_iSup_generalizedEigenspace_of_comm rfl μ)) :=
    restrict_commute h_comm.symm _ _
  rw [restrict_comp, trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm
    (f.isNilpotent_restrict_iSup_sub_algebraMap μ), hg, mul_zero]

end LinearMap
