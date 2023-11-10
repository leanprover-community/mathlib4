import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Finiteness

open BigOperators DirectSum
open LinearMap (trace)

variable {ι : Type*} (R M : Type*) [CommRing R]

namespace Matrix

lemma trace_blockDiagonal' {o : Type*} {m' : o → Type*} {α : Type*} [Fintype o] [∀ i, Fintype (m' i)]
    [DecidableEq o] [AddCommMonoid α] (M : ∀ i, Matrix (m' i) (m' i) α) :
    trace (blockDiagonal' M) = ∑ i, trace (M i) := by
  simp [blockDiagonal', trace, Finset.sum_sigma']

end Matrix

variable {R M}
variable [AddCommGroup M] [Module R M]
  {N : ι → Submodule R M} [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

lemma bar' [Fintype ι]
    (h_ind : CompleteLattice.Independent N)
    (h_sup : ⨆ i, N i = ⊤)
    {f : M →ₗ[R] M} (hf : ∀ i, Set.MapsTo f (N i) (N i)) :
    trace R M f = ∑ i, trace R (N i) (f.restrict (hf i)) := by
  have : DecidableEq ι := Classical.decEq ι
  have h := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top h_ind h_sup
  let b : Basis _ R M := h.collectedBasis <| fun i ↦ Module.Free.chooseBasis R (N i)
  suffices LinearMap.toMatrix b b f = Matrix.blockDiagonal' fun i ↦ LinearMap.toMatrix
      (Module.Free.chooseBasis R (N i)) (Module.Free.chooseBasis R (N i)) (f.restrict (hf i)) by
    simp_rw [LinearMap.trace_eq_matrix_trace R b, this, Matrix.trace_blockDiagonal',
      ← LinearMap.trace_eq_matrix_trace]
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [LinearMap.toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h.collectedBasis_repr_of_mem _ (hf i (Subtype.mem _)), LinearMap.restrict_apply]
  · simp [hij, h.collectedBasis_repr_of_mem_ne _ hij.symm (hf j (Subtype.mem _))]

variable [IsNoetherian R M] -- TODO Drop this where redundant

lemma foo' (h_ind : CompleteLattice.Independent N) :
    Set.Finite {i | N i ≠ ⊥} :=
  CompleteLattice.WellFounded.finite_ne_bot_of_independent
    (isNoetherian_iff_wellFounded.mp inferInstance) h_ind

lemma bar''
    (h_ind : CompleteLattice.Independent N)
    (h_sup : ⨆ i, N i = ⊤)
    {f : M →ₗ[R] M} (hf : ∀ i, Set.MapsTo f (N i) (N i))
    (h_fin : Set.Finite {i | N i ≠ ⊥} := foo' h_ind) :
    trace R M f = ∑ i in h_fin.toFinset, trace R (N i) (f.restrict (hf i)) := by
  set s : Finset ι := h_fin.toFinset
  replace h_ind : CompleteLattice.Independent (fun i : s ↦ N i) := h_ind.comp Subtype.val_injective
  replace h_sup : ⨆ (i : s), N i = ⊤ := by
    have : ⨆ i, ⨆ (_ : N i = ⊥), N i = ⊥ := by simp [iSup_eq_bot]
    rw [iSup_split _ (fun i ↦ N i = ⊥), this, bot_sup_eq] at h_sup
    simpa [iSup_subtype]
  rw [← Finset.sum_coe_sort, bar' h_ind h_sup (fun i ↦ hf i)]

-- Option A: make this definition + develop its API
-- Option B: prove lemma about any map `(⨁ i, N i) →ₗ[R] (⨁ i, N i)` satisfying the characteristic
-- properties of this definition. I think I pefer B.
-- def baz {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
--     [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]
--     [DecidableEq ι] (f : (i : ι) → N i →ₗ[R] N i) :
--     (⨁ i, N i) →ₗ[R] (⨁ i, N i) :=
--   DirectSum.toModule R ι _ <| fun i ↦ DirectSum.lof R ι N i ∘ₗ (f i)

/-

-- NB: `Basis.prod` already exists and `Basis.pi` does not. This would mathematically coincide
-- with `Basis.pi` when `ι` was finite.
-- Should this be used to golf `DirectSum.IsInternal.collectedBasis`?
variable {R M} in
noncomputable def Basis.directSum
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (N i)) :
    Basis ((i : ι) × κ i) R (⨁ i, N i) :=
  ⟨(DFinsupp.mapRange.linearEquiv fun i ↦ (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm⟩

lemma LinearMap.toMatrix_directSum
    {N₁ : ι → Type*} [∀ i, AddCommGroup (N₁ i)] [∀ i, Module R (N₁ i)]
    {N₂ : ι → Type*} [∀ i, AddCommGroup (N₂ i)] [∀ i, Module R (N₂ i)]
    {κ₁ : ι → Type*} (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i))
    {κ₂ : ι → Type*} (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
    (f : (i : ι) → N₁ i →ₗ[R] N₂ i) (g : (⨁ i, N₁ i) →ₗ[R] (⨁ i, N₂ i))
    [Fintype ι] [∀ i, Fintype (κ₁ i)] [∀ i, Fintype (κ₂ i)]
    [DecidableEq ι] [∀ i, DecidableEq (κ₁ i)] -- [∀ i, DecidableEq (κ₂ i)]
    (hg₁ : ∀ i j, i ≠ j → component R ι N₂ j ∘ₗ g ∘ₗ lof R ι N₁ i = 0)
    (hg₂ : ∀ i, component R ι N₂ i ∘ₗ g ∘ₗ lof R ι N₁ i = f i) :
    LinearMap.toMatrix (Basis.directSum b₁) (Basis.directSum b₂) g =
    Matrix.blockDiagonal' fun i ↦ LinearMap.toMatrix (b₁ i) (b₂ i) (f i) := by
  classical -- Not sure if necessary
  ext ⟨i, k₁⟩ ⟨j, k₂⟩
  simp only [Basis.directSum, Matrix.blockDiagonal'_apply, Matrix.of_apply, toMatrix_apply,
    Basis.coe_ofRepr, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    sigmaFinsuppLequivDFinsupp_apply, sigmaFinsuppEquivDFinsupp_single,
    sigmaFinsuppLequivDFinsupp_symm_apply, sigmaFinsuppEquivDFinsupp_symm_apply]
  rcases eq_or_ne i j with rfl | hij
  · --simp only [← hg₂ i, cast_eq, dite_eq_ite, ite_true]
    simp only [cast_eq, dite_eq_ite, ite_true]
    erw [DFinsupp.mapRange.linearEquiv_apply] -- Shouldn't need `erw` :-(
    simp only [DFinsupp.mapRange_apply]
    congr


    sorry
  · simp only [hij, dite_false]
    erw [DFinsupp.mapRange.linearEquiv_apply] -- Shouldn't need `erw` :-(
    simp only [DFinsupp.mapRange_apply]

    sorry

lemma qux
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Free R (N i)]
    [∀ i, Module.Finite R (N i)]
    (f : (i : ι) → N i →ₗ[R] N i) (g : (⨁ i, N i) →ₗ[R] (⨁ i, N i))
    [DecidableEq ι]
    (hg₁ : ∀ i j, i ≠ j → DirectSum.component R ι N j ∘ₗ g ∘ₗ DirectSum.lof R ι N i = 0)
    (hg₂ : ∀ i, DirectSum.component R ι N i ∘ₗ g ∘ₗ DirectSum.lof R ι N i = f i)
    (h_fin : Set.Finite {i | f i ≠ 0}) :
    trace R _ g = ∑ i in h_fin.toFinset, trace R _ (f i) := by
  let b := fun i ↦ Module.Free.chooseBasis R (N i)
  let B := Basis.directSum b
  sorry

-/
