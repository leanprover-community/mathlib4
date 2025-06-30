/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Map
import Mathlib.Logic.Embedding.Set

/-!
# Sums of matroids

The *sum* `M` of a collection `M₁, M₂, ..` of matroids is a matroid on the disjoint union of
the ground sets of the summands, in which the independent sets are precisely the unions of
independent sets of the summands.

We can ask for such a sum both for pairs and for arbitrary indexed collections of matroids,
and we can also ask for the 'disjoint union' to be either set-theoretic or type-theoretic.
To this end, we define five separate versions of the sum construction.

## Main definitions

* For an indexed collection `M : (i : ι) → Matroid (α i)` of matroids on different types,
  `Matroid.sigma M` is the sum of the `M i`, as a matroid on the sigma type `(Σ i, α i)`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type,
  `Matroid.sum' M` is the sum of the `M i`, as a matroid on the product type `ι × α`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type, and a
  proof `h : Pairwise (Disjoint on fun i ↦ (M i).E)` that they have disjoint ground sets,
  `Matroid.disjointSigma M h` is the sum of the `M` as a `Matroid α` with ground set `⋃ i, (M i).E`.

* `Matroid.sum (M : Matroid α) (N : Matroid β)` is the sum of `M` and `N` as a matroid on `α ⊕ β`.

* If `M N : Matroid α` and `h : Disjoint M.E N.E`, then `Matroid.disjointSum M N h` is the sum
  of `M` and `N` as a `Matroid α` with ground set `M.E ∪ N.E`.

## Implementation details

We only directly define a matroid for `Matroid.sigma`. All other versions of sum are
defined indirectly, using `Matroid.sigma` and the API in `Matroid.map`.
-/

assert_not_exists Field

universe u v

open Set
namespace Matroid

section Sigma

variable {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)}

/-- The sum of an indexed collection of matroids, as a matroid on the sigma-type. -/
protected def sigma (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) where
  E := univ.sigma (fun i ↦ (M i).E)
  Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
  IsBase B := ∀ i, (M i).IsBase (Sigma.mk i ⁻¹' B)

  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, hB, hIB⟩ i ↦ (hB i).indep.subset (preimage_mono hIB)⟩
    choose Bs hBs using fun i ↦ (h i).exists_isBase_superset
    refine ⟨univ.sigma Bs, fun i ↦ by simpa using (hBs i).1, ?_⟩
    rw [← univ_sigma_preimage_mk I]
    refine sigma_mono rfl.subset fun i ↦ (hBs i).2

  exists_isBase := by
    choose B hB using fun i ↦ (M i).exists_isBase
    exact ⟨univ.sigma B, by simpa⟩

  isBase_exchange B₁ B₂ h₁ h₂ := by
    simp only [mem_diff, Sigma.exists, and_imp, Sigma.forall]
    intro i e he₁ he₂
    have hf_ex := (h₁ i).exchange (h₂ i) ⟨he₁, by simpa⟩
    obtain ⟨f, ⟨hf₁, hf₂⟩, hfB⟩ := hf_ex
    refine ⟨i, f, ⟨hf₁, hf₂⟩, fun j ↦ ?_⟩
    rw [← union_singleton, preimage_union, preimage_diff]
    obtain (rfl | hne) := eq_or_ne i j
    · simpa only [ show ∀ x, {⟨i,x⟩} = Sigma.mk i '' {x} by simp,
        preimage_image_eq _ sigma_mk_injective, union_singleton]
    rw [preimage_singleton_eq_empty.2 (by simpa), preimage_singleton_eq_empty.2 (by simpa),
      diff_empty, union_empty]
    exact h₁ j

  maximality X _ I hI hIX := by
    choose Js hJs using
      fun i ↦ (hI i).subset_isBasis'_of_subset (preimage_mono (f := Sigma.mk i) hIX)
    use univ.sigma Js
    simp only [maximal_subset_iff', mem_univ, mk_preimage_sigma, and_imp]
    refine ⟨?_, ⟨fun i ↦ (hJs i).1.indep, ?_⟩, fun S hS hSX hJS ↦ ?_⟩
    · rw [← univ_sigma_preimage_mk I]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).2
    · rw [← univ_sigma_preimage_mk X]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).1.subset
    rw [← univ_sigma_preimage_mk S]
    refine sigma_mono rfl.subset fun i ↦ ?_
    rw [sigma_subset_iff] at hJS
    rw [(hJs i).1.eq_of_subset_indep (hS i) (hJS <| mem_univ i)]
    exact preimage_mono hSX

  subset_ground B hB := by
    rw [← univ_sigma_preimage_mk B]
    apply sigma_mono Subset.rfl fun i ↦ (hB i).subset_ground

@[simp] lemma sigma_indep_iff {I} :
    (Matroid.sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := Iff.rfl

@[simp] lemma sigma_isBase_iff {B} :
    (Matroid.sigma M).IsBase B ↔ ∀ i, (M i).IsBase (Sigma.mk i ⁻¹' B) := Iff.rfl

@[simp] lemma sigma_ground_eq : (Matroid.sigma M).E = univ.sigma fun i ↦ (M i).E := rfl

@[simp] lemma sigma_isBasis_iff {I X} :
    (Matroid.sigma M).IsBasis I X ↔ ∀ i, (M i).IsBasis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  simp only [IsBasis, sigma_indep_iff, maximal_subset_iff, and_imp, and_assoc, sigma_ground_eq,
    forall_and, and_congr_right_iff]
  refine fun hI ↦ ⟨fun ⟨hIX, h, h'⟩ ↦ ⟨fun i ↦ preimage_mono hIX, fun i I₀ hI₀ hI₀X hII₀ ↦ ?_, ?_⟩,
    fun ⟨hIX, h', h''⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · refine hII₀.antisymm ?_
    specialize h (t := I ∪ Sigma.mk i '' I₀)
    simp only [preimage_union, union_subset_iff, hIX, image_subset_iff, hI₀X, and_self,
      subset_union_left, true_implies] at h
    rw [h, preimage_union, sigma_mk_preimage_image_eq_self]
    · exact subset_union_right
    intro j
    obtain (rfl | hij) := eq_or_ne i j
    · rwa [sigma_mk_preimage_image_eq_self, union_eq_self_of_subset_left hII₀]
    rw [sigma_mk_preimage_image' hij, union_empty]
    apply hI
  · exact fun i ↦ by simpa using preimage_mono (f := Sigma.mk i) h'
  · exact fun ⟨i, x⟩ hx ↦ by simpa using hIX i hx
  · refine fun J hJ hJX hIJ ↦ hIJ.antisymm fun ⟨i,x⟩ hx ↦ ?_
    simpa using (h' i (hJ i) (preimage_mono hJX) (preimage_mono hIJ)).symm.subset hx
  exact fun ⟨i,x⟩ hx ↦ by simpa using h'' i hx

lemma Finitary.sigma (h : ∀ i, (M i).Finitary) : (Matroid.sigma M).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [sigma_indep_iff] at hI ⊢
  intro i
  apply indep_of_forall_finite_subset_indep
  intro J hJI hJ
  convert hI (Sigma.mk i '' J) (by simpa) (hJ.image _) i
  rw [sigma_mk_preimage_image_eq_self]

end Sigma

section sum'

variable {α ι : Type*} {M : ι → Matroid α}

/-- The sum of an indexed family `M : ι → Matroid α` of matroids on the same type,
as a matroid on the product type `ι × α`. -/
protected def sum' (M : ι → Matroid α) : Matroid (ι × α) :=
  (Matroid.sigma M).mapEquiv <| Equiv.sigmaEquivProd ι α

@[simp] lemma sum'_indep_iff {I} :
    (Matroid.sum' M).Indep I ↔ ∀ i, (M i).Indep (Prod.mk i ⁻¹' I) := by
  simp only [Matroid.sum', mapEquiv_indep_iff, Equiv.sigmaEquivProd_symm_apply, sigma_indep_iff]
  convert Iff.rfl
  ext
  simp

@[simp] lemma sum'_ground_eq (M : ι → Matroid α) :
    (Matroid.sum' M).E = ⋃ i, Prod.mk i '' (M i).E := by
  ext
  simp [Matroid.sum']

@[simp] lemma sum'_isBase_iff {B} :
    (Matroid.sum' M).IsBase B ↔ ∀ i, (M i).IsBase (Prod.mk i ⁻¹' B) := by
  simp only [Matroid.sum', mapEquiv_isBase_iff, Equiv.sigmaEquivProd_symm_apply, sigma_isBase_iff]
  convert Iff.rfl
  ext
  simp

@[simp] lemma sum'_isBasis_iff {I X} :
    (Matroid.sum' M).IsBasis I X ↔ ∀ i, (M i).IsBasis (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X) := by
  simp only [Matroid.sum', mapEquiv_isBasis_iff, Equiv.sigmaEquivProd_symm_apply, sigma_isBasis_iff]
  convert Iff.rfl <;>
  exact ext <| by simp

lemma Finitary.sum' (h : ∀ i, (M i).Finitary) : (Matroid.sum' M).Finitary := by
  have := Finitary.sigma h
  rw [Matroid.sum']
  infer_instance

end sum'

section disjointSigma

open scoped Function -- required for scoped `on` notation

variable {α ι : Type*} {M : ι → Matroid α}

/-- The sum of an indexed collection of matroids on `α` with pairwise disjoint ground sets,
as a matroid on `α` -/
protected def disjointSigma (M : ι → Matroid α) (h : Pairwise (Disjoint on fun i ↦ (M i).E)) :
    Matroid α :=
  (Matroid.sigma (fun i ↦ (M i).restrictSubtype (M i).E)).mapEmbedding
    (Function.Embedding.sigmaSet h)

@[simp] lemma disjointSigma_ground_eq {h} : (Matroid.disjointSigma M h).E = ⋃ i : ι, (M i).E := by
  ext; simp [Matroid.disjointSigma, mapEmbedding, restrictSubtype]

@[simp] lemma disjointSigma_indep_iff {h I} :
    (Matroid.disjointSigma M h).Indep I ↔
      (∀ i, (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, (Function.Embedding.sigmaSet_preimage h)]

@[simp] lemma disjointSigma_isBase_iff {h B} :
    (Matroid.disjointSigma M h).IsBase B ↔
      (∀ i, (M i).IsBase (B ∩ (M i).E)) ∧ B ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, (Function.Embedding.sigmaSet_preimage h)]

@[simp] lemma disjointSigma_isBasis_iff {h I X} :
    (Matroid.disjointSigma M h).IsBasis I X ↔
      (∀ i, (M i).IsBasis (I ∩ (M i).E) (X ∩ (M i).E)) ∧ I ⊆ X ∧ X ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, Function.Embedding.sigmaSet_preimage h]

end disjointSigma

section Sum

variable {α : Type u} {β : Type v} {M N : Matroid α}

/-- The sum of two matroids as a matroid on the sum type. -/
protected def sum (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
  let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
  (S.mapEquiv e.symm).mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)

@[simp] lemma sum_ground (M : Matroid α) (N : Matroid β) :
    (M.sum N).E = (.inl '' M.E) ∪ (.inr '' N.E) := by
  simp [Matroid.sum, Set.ext_iff, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_indep_iff (M : Matroid α) (N : Matroid β) {I : Set (α ⊕ β)} :
    (M.sum N).Indep I ↔ M.Indep (.inl ⁻¹' I) ∧ N.Indep (.inr ⁻¹' I) := by
  simp only [Matroid.sum, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool]
  convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_isBase_iff {M : Matroid α} {N : Matroid β} {B : Set (α ⊕ β)} :
    (M.sum N).IsBase B ↔ M.IsBase (.inl ⁻¹' B) ∧ N.IsBase (.inr ⁻¹' B) := by
  simp only [Matroid.sum, mapEquiv_isBase_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_isBase_iff, Bool.forall_bool]
  convert Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

@[simp] lemma sum_isBasis_iff {M : Matroid α} {N : Matroid β} {I X : Set (α ⊕ β)} :
    (M.sum N).IsBasis I X ↔
      (M.IsBasis (Sum.inl ⁻¹' I) (Sum.inl ⁻¹' X) ∧ N.IsBasis (Sum.inr ⁻¹' I) (Sum.inr ⁻¹' X)) := by
  simp only [Matroid.sum, mapEquiv_isBasis_iff, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Equiv.symm_symm, sigma_isBasis_iff, Bool.forall_bool,
    Equiv.sumEquivSigmaBool, Equiv.coe_fn_mk, Equiv.ulift]
  convert Iff.rfl <;> exact ext <| by simp

end Sum

section disjointSum

variable {α : Type*} {M N : Matroid α}

/-- The sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`. -/
def disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.restrictSubtype M.E).sum (N.restrictSubtype N.E)).mapEmbedding <| Function.Embedding.sumSet h

@[simp] lemma disjointSum_ground_eq {h} : (M.disjointSum N h).E = M.E ∪ N.E := by
  simp [disjointSum, restrictSubtype, mapEmbedding]

@[simp] lemma disjointSum_indep_iff {h I} :
    (M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

@[simp] lemma disjointSum_isBase_iff {h B} :
    (M.disjointSum N h).IsBase B ↔ M.IsBase (B ∩ M.E) ∧ N.IsBase (B ∩ N.E) ∧ B ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

@[simp] lemma disjointSum_isBasis_iff {h I X} :
    (M.disjointSum N h).IsBasis I X ↔ M.IsBasis (I ∩ M.E) (X ∩ M.E) ∧
      N.IsBasis (I ∩ N.E) (X ∩ N.E) ∧ I ⊆ X ∧ X ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]

lemma disjointSum_comm {h} : M.disjointSum N h = N.disjointSum M h.symm := by
  ext
  · simp [union_comm]
  repeat simpa [union_comm] using ⟨fun ⟨m, n, h⟩ ↦ ⟨n, m, M.E.union_comm N.E ▸ h⟩,
    fun ⟨n, m, h⟩ ↦ ⟨m, n, M.E.union_comm N.E ▸ h⟩⟩

lemma Indep.eq_union_image_of_disjointSum {h I} (hI : (disjointSum M N h).Indep I) :
    ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧ I = IM ∪ IN := by
  rw [disjointSum_indep_iff] at hI
  refine ⟨_, _, hI.1, hI.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hI.2.2]

lemma IsBase.eq_union_image_of_disjointSum {h B} (hB : (disjointSum M N h).IsBase B) :
    ∃ BM BN, M.IsBase BM ∧ N.IsBase BN ∧ Disjoint BM BN ∧ B = BM ∪ BN := by
  rw [disjointSum_isBase_iff] at hB
  refine ⟨_, _, hB.1, hB.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hB.2.2]

end disjointSum

end Matroid
