/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Linear maps between direct sums

This file contains results about linear maps which respect direct sum decompositions of their
domain and codomain.

-/

open DirectSum Module Set

namespace LinearMap

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

section IsInternal

variable [DecidableEq ι]

/-- If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decompositions. -/
lemma toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Finite (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
    [Fintype ι] (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h₂.collectedBasis_repr_of_mem _ (hf _ (Subtype.mem _)), restrict_apply]
  · simp [hij, h₂.collectedBasis_repr_of_mem_ne _ hij.symm (hf _ (Subtype.mem _))]

lemma diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {s : Finset ι} (h : IsInternal fun i : s ↦ N i)
    (b : (i : s) → Basis (κ i) R (N i)) (σ : ι → ι) (hσ : ∀ i, σ i ≠ i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N <| σ i)) (hN : ∀ i, i ∉ s → N i = ⊥) :
    Matrix.diag (toMatrix (h.collectedBasis b) (h.collectedBasis b) f) = 0 := by
  ext ⟨i, k⟩
  simp only [Matrix.diag_apply, Pi.zero_apply, toMatrix_apply, IsInternal.collectedBasis_coe]
  by_cases hi : σ i ∈ s
  · let j : s := ⟨σ i, hi⟩
    replace hσ : j ≠ i := fun hij ↦ hσ i <| Subtype.ext_iff.mp hij
    exact h.collectedBasis_repr_of_mem_ne b hσ <| hf _ <| Subtype.mem (b i k)
  · suffices f (b i k) = 0 by simp [this]
    simpa [hN _ hi] using hf i <| Subtype.mem (b i k)

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

/-- The trace of an endomorphism of a direct sum is the sum of the traces on each component.

See also `LinearMap.trace_restrict_eq_sum_trace_restrict`. -/
lemma trace_eq_sum_trace_restrict (h : IsInternal N) [Fintype ι]
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i, trace R (N i) (f.restrict (hf i)) := by
  let b : (i : ι) → Basis _ R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b),
    toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hf, Matrix.trace_blockDiagonal',
    ← trace_eq_matrix_trace]

lemma trace_eq_sum_trace_restrict' (h : IsInternal N) (hN : {i | N i ≠ ⊥}.Finite)
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i ∈ hN.toFinset, trace R (N i) (f.restrict (hf i)) := by
  let _ : Fintype {i // N i ≠ ⊥} := hN.fintype
  let _ : Fintype {i | N i ≠ ⊥} := hN.fintype
  rw [← Finset.sum_coe_sort, trace_eq_sum_trace_restrict (isInternal_ne_bot_iff.mpr h) (hf ·)]
  exact Fintype.sum_equiv hN.subtypeEquivToFinset _ _ (fun i ↦ rfl)

lemma trace_eq_zero_of_mapsTo_ne (h : IsInternal N) [IsNoetherian R M]
    (σ : ι → ι) (hσ : ∀ i, σ i ≠ i) {f : Module.End R M}
    (hf : ∀ i, MapsTo f (N i) (N <| σ i)) :
    trace R M f = 0 := by
  have hN : {i | N i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep
    h.submodule_iSupIndep
  let s := hN.toFinset
  let κ := fun i ↦ Module.Free.ChooseBasisIndex R (N i)
  let b : (i : s) → Basis (κ i) R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  replace h : IsInternal fun i : s ↦ N i := by
    convert DirectSum.isInternal_ne_bot_iff.mpr h <;> simp [s]
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b), Matrix.trace,
    diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne h b σ hσ hf (by simp [s]),
    Pi.zero_apply, Finset.sum_const_zero]

/-- If `f` and `g` are commuting endomorphisms of a finite, free `R`-module `M`, such that `f`
is triangularizable, then to prove that the trace of `g ∘ f` vanishes, it is sufficient to prove
that the trace of `g` vanishes on each generalized eigenspace of `f`. -/
lemma trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
    {f g : Module.End R M}
    (h_comm : Commute f g)
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤)
    (hg : ∀ μ, trace R _ (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ)) = 0) :
    trace R _ (g ∘ₗ f) = 0 := by
  have hfg : ∀ μ,
      MapsTo (g ∘ₗ f) ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ ↦ (f.mapsTo_maxGenEigenspace_of_comm h_comm μ).comp
      (f.mapsTo_maxGenEigenspace_of_comm rfl μ)
  suffices ∀ μ, trace R _ ((g ∘ₗ f).restrict (hfg μ)) = 0 by
    classical
    have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace hf
    have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
      WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
    simp [trace_eq_sum_trace_restrict' hds h_fin hfg, this]
  intro μ
  have hf' := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hg' := f.mapsTo_maxGenEigenspace_of_comm h_comm μ
  replace h_comm : Commute (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ))
      (f.restrict (f.mapsTo_maxGenEigenspace_of_comm rfl μ)) :=
    restrict_commute h_comm.symm _ _
  have := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  rw [restrict_comp hf' hg', trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm this,
    hg, mul_zero]

lemma mapsTo_biSup_of_mapsTo {ι : Type*} {N : ι → Submodule R M}
    (s : Set ι) {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    MapsTo f ↑(⨆ i ∈ s, N i) ↑(⨆ i ∈ s, N i) := by
  replace hf : ∀ i, (N i).map f ≤ N i := fun i ↦ Submodule.map_le_iff_le_comap.mpr (hf i)
  suffices (⨆ i ∈ s, N i).map f ≤ ⨆ i ∈ s, N i from Submodule.map_le_iff_le_comap.mp this
  simpa only [Submodule.map_iSup] using iSup₂_mono <| fun i _ ↦ hf i

end IsInternal

/-- The trace of an endomorphism of a direct sum is the sum of the traces on each component.

Note that it is important the statement gives the user definitional control over `p` since the
_type_ of the term `trace R p (f.restrict hp')` depends on `p`. -/
lemma trace_eq_sum_trace_restrict_of_eq_biSup
    [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]
    (s : Finset ι) (h : iSupIndep <| fun i : s ↦ N i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i))
    (p : Submodule R M) (hp : p = ⨆ i ∈ s, N i)
    (hp' : MapsTo f p p := hp ▸ mapsTo_biSup_of_mapsTo (s : Set ι) hf) :
    trace R p (f.restrict hp') = ∑ i ∈ s, trace R (N i) (f.restrict (hf i)) := by
  classical
  let N' : s → Submodule R p := fun i ↦ (N i).comap p.subtype
  replace h : IsInternal N' := hp ▸ isInternal_biSup_submodule_of_iSupIndep (s : Set ι) h
  have hf' : ∀ i, MapsTo (restrict f hp') (N' i) (N' i) := fun i x hx' ↦ by simpa using hf i hx'
  let e : (i : s) → N' i ≃ₗ[R] N i := fun ⟨i, hi⟩ ↦ (N i).comapSubtypeEquivOfLe (hp ▸ le_biSup N hi)
  have _i1 : ∀ i, Module.Finite R (N' i) := fun i ↦ Module.Finite.equiv (e i).symm
  have _i2 : ∀ i, Module.Free R (N' i) := fun i ↦ Module.Free.of_equiv (e i).symm
  rw [trace_eq_sum_trace_restrict h hf', ← s.sum_coe_sort]
  have : ∀ i : s, f.restrict (hf i) = (e i).conj ((f.restrict hp').restrict (hf' i)) := fun _ ↦ rfl
  simp [this]

end LinearMap
