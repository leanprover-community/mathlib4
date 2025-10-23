/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.Finite.Sigma
import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact open covered sets

In this file we define the notion of a compact-open covered set with respect to a family of
maps `fᵢ : X i → S`. A set `U` is compact-open covered by the family `fᵢ` if it is the finite
union of images of compact open sets in the `X i`.

This notion is not interesting, if the `fᵢ` are open maps (see `IsCompactOpenCovered.of_isOpenMap`).

This is used to define the fpqc topology of schemes, there a cover is given by a family of flat
morphisms such that every compact open is compact-open covered.

## Main results

- `IsCompactOpenCovered.of_isOpenMap`: If all the `fᵢ` are open maps, then every compact open
  of `S` is compact-open covered.
-/

open TopologicalSpace Opens

lemma PrespectralSpace.exists_isCompact_and_isOpen_between {X : Type*} [TopologicalSpace X]
    [PrespectralSpace X] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hUV : K ⊆ U) :
    ∃ (W : Set X), IsCompact W ∧ IsOpen W ∧ W ⊆ U ∧ K ⊆ W := by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hWU, hKW⟩ ↦ ?_) ?_ ?_
  · use W, Wc, Wo, hWU, subset_trans hst hKW
  · intro s t ⟨W₁, Wc₁, Wo₁, hWU₁, hKW₁⟩ ⟨W₂, Wc₂, Wo₂, hWU₂, hKW₂⟩
    exact ⟨W₁ ∪ W₂, Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset hWU₁ hWU₂,
      Set.union_subset_union hKW₁ hKW₂⟩
  · intro x hx
    obtain ⟨V, h, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hUV hx) hU
    exact ⟨V, mem_nhdsWithin.mpr ⟨V, h.1, hxV, Set.inter_subset_left⟩, V, h.2, h.1, hVU, subset_rfl⟩

/-- A set `U` is compact-open covered by the family `fᵢ : X i → S`, if
`U` is the finite union of images of compact open sets in the `X i`. -/
def IsCompactOpenCovered {S ι : Type*} {X : ι → Type*} (f : ∀ i, X i → S)
    [∀ i, TopologicalSpace (X i)] (U : Set S) : Prop :=
  ∃ (s : Set ι) (_ : s.Finite) (V : ∀ i ∈ s, Opens (X i)),
    (∀ (i : ι) (h : i ∈ s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i ∈ s), (f i) '' (V i h) = U

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι → Type*} {f : ∀ i, X i → S} [∀ i, TopologicalSpace (X i)] {U : Set S}

lemma empty : IsCompactOpenCovered f ∅ :=
  ⟨∅, Set.finite_empty, fun _ _ ↦ ⟨∅, isOpen_empty⟩, fun _ _ ↦ isCompact_empty, by simp⟩

lemma iff_of_unique [Unique ι] :
    IsCompactOpenCovered f U ↔ ∃ (V : Opens (X default)), IsCompact V.1 ∧ f default '' V.1 = U := by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ ↦ ?_, fun ⟨V, hc, h⟩ ↦ ?_⟩
  · by_cases h : s = ∅
    · aesop
    · obtain rfl : s = {default} := by
        rw [← Set.univ_unique, Subsingleton.eq_univ_of_nonempty (Set.nonempty_iff_ne_empty.mpr h)]
      aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h ↦ h ▸ V, fun i ↦ ?_, by simpa⟩
    rintro rfl
    simpa

lemma id_iff_isOpen_and_isCompact [TopologicalSpace S] :
    IsCompactOpenCovered (fun _ : Unit ↦ id) U ↔ IsOpen U ∧ IsCompact U := by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ ↦ ?_, fun ⟨ho, hc⟩ ↦ ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩

lemma iff_isCompactOpenCovered_sigmaMk :
    IsCompactOpenCovered f U ↔
      IsCompactOpenCovered (fun (_ : Unit) (p : Σ i : ι, X i) ↦ f p.1 p.2) U := by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ ↦ ?_, fun ⟨V, hc, heq⟩ ↦ ?_⟩
  · refine ⟨⟨s.sigma fun i ↦ if h : i ∈ s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i ∈ s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i ↦ (by simp_all)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i ∈ s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi ↦ ⟨t i, this i hi⟩, fun i _ ↦ hc i, ?_⟩
    simp_rw [coe_mk, ← heq, ← heq', Set.image_sigma_eq_iUnion, Function.comp_apply]

lemma of_iUnion_eq_of_finite (s : Set (Set S)) (hs : ⋃ t ∈ s, t = U) (hf : s.Finite)
    (H : ∀ t ∈ s, IsCompactOpenCovered f t) : IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  have (t) (h : t ∈ s) : ∃ (V : Opens (Σ i, X i)),
      IsCompact V.1 ∧ (fun p ↦ f p.fst p.snd) '' V.carrier = t := by
    have := H t h
    rwa [iff_isCompactOpenCovered_sigmaMk, iff_of_unique] at this
  choose V hVeq hVc using this
  refine ⟨⨆ (t : s), V t t.2, ?_, ?_⟩
  · simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    have : Finite s := hf
    exact isCompact_iUnion (fun _ ↦ hVeq _ _)
  · simp [Set.image_iUnion, ← hs]
    simp_all

lemma of_iUnion_eq_of_isCompact [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (s : Set (Opens S)) (hs : ⋃ t ∈ s, t = U) (H : ∀ t ∈ s, IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s ↦ V.1) (fun V ↦ V.1.2) (by simp [← hs])
  refine of_iUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x h ↦ by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · grind

lemma of_isCompact_of_forall_exists [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (H : ∀ x ∈ U, ∃ t ⊆ U, x ∈ t ∧ IsOpen t ∧ IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  choose Us hU' hUx hUo hU'' using H
  refine of_iUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x ∈ U) } ?_ ?_
  · refine subset_antisymm (fun x ↦ ?_) fun x hx ↦ ?_
    · simp only [Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
        exists_and_right, forall_exists_index, and_imp]
      intro V y hy heq hyV
      apply hU' y hy
      rwa [heq]
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · simp only [Set.mem_setOf_eq, forall_exists_index]
    intro t x hx heq
    rw [← heq]
    exact hU'' _ _

lemma of_finite {U : Set S} {κ : Type*} [Finite κ] (a : κ → ι) (V : ∀ k, Opens (X (a k)))
    (hV : ∀ k, IsCompact (V k).1) (hU : ⋃ k, f (a k) '' V k = U) :
    IsCompactOpenCovered f U := by
  refine ⟨Set.range a, Set.finite_range a, fun i hi ↦ ⨆ (k : κ) (h : i = a k), h ▸ V k,
      fun i hi ↦ ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    refine isCompact_iUnion fun i ↦ isCompact_iUnion ?_
    rintro rfl
    exact hV _
  · simp only [Set.mem_range, iSup_mk, carrier_eq_coe, coe_mk, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', ← hU]
    ext x
    simp_rw [Set.image_iUnion, Set.mem_iUnion]
    refine ⟨fun ⟨i, j, h, y, hy, hyx⟩ ↦ ⟨j, h ▸ y, ?_, ?_⟩, fun ⟨m, y, h, e⟩ ↦ ⟨m, m, rfl, y, h, e⟩⟩
    · simp only [SetLike.mem_coe] at hy ⊢
      convert hy using 1 <;> try rw [h]
      repeat simp
    · rw [← hyx]
      congr 1 <;> simp [h]

/-- If `U` is compact-open covered and the `X i` have a basis of compact opens,
`U` can be written as the union of images of elements of the basis. -/
lemma exists_mem_of_isBasis {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1)
    {U : Set S} (hU : IsCompactOpenCovered f U) :
    ∃ (n : ℕ) (a : Fin n → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ ⋃ i, f (a i) '' V i = U := by
  suffices h : ∃ (κ : Type _) (_ : Finite κ) (a : κ → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i ↦ V _, fun i ↦ hB _, ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s ↦ (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i : _) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i ↦ i.1.1, fun i ↦ i.2.1, fun i ↦ UsB _ (by simp),
      fun _ ↦ hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ ↦ by aesop, fun ⟨i, hi, h, hmem, heq⟩ ↦ ?_⟩
  rw [hUs ⟨i, hi⟩, coe_sSup, Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

lemma of_finite_of_isSpectralMap [Finite ι] [TopologicalSpace S] [∀ i, PrespectralSpace (X i)]
    (hf : ∀ i, IsSpectralMap (f i)) {U : Set S} (hs : ∀ x ∈ U, ∃ i, x ∈ Set.range (f i))
    (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  refine ⟨.univ, Set.finite_univ, fun i _ ↦ ⟨f i ⁻¹' U, hU.preimage (hf i).1⟩,
    fun i _ ↦ hc.preimage_of_isOpen (hf i) hU, subset_antisymm (by simp) fun x hx ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hs x hx
  simpa using ⟨i, y, hx, rfl⟩

lemma of_isOpenMap [TopologicalSpace S] [∀ i, PrespectralSpace (X i)]
    (hfc : ∀ i, Continuous (f i)) (h : ∀ i, IsOpenMap (f i))
    {U : Set S} (hs : ∀ x ∈ U, ∃ i, x ∈ Set.range (f i)) (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_prespectralSpace
      (continuous_sigma_iff.mpr hfc) (fun x hx ↦ ?_) hU hc
  simpa using hs x hx

/-- Being compact open covered descends along refinements if the spaces are prespectral. -/
lemma of_comp [∀ i, PrespectralSpace (X i)] [TopologicalSpace S]
    {σ : Type*} {Y : σ → Type*} [∀ i, TopologicalSpace (Y i)]
    (g : ∀ i, Y i → S) {a : σ → ι} (t : ∀ i, Y i → X (a i)) (ht : ∀ i, Continuous (t i))
    (hge : ∀ i, g i = f (a i) ∘ t i)
    (hf : ∀ i, Continuous (f i)) {U : Set S} (ho : IsOpen U) (hU : IsCompactOpenCovered g U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) → (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x ↦ f x.1 x.2) ∘ p = fun x ↦ g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i ↦ f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hKU, hVK⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
      (hV.image hp) (ho.preimage hf) <| by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq, ← hcomp, Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

end IsCompactOpenCovered
