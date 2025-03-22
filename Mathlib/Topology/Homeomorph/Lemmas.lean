/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.DenseEmbedding

/-!
# Further properties of homeomorphisms

This file proves further properties of homeomorphisms between topological spaces.
Pretty much every topological property is preserved under homeomorphisms.

-/

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*}

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/-- Homeomorphism given an embedding. -/
noncomputable def ofIsEmbedding (f : X → Y) (hf : IsEmbedding f) : X ≃ₜ Set.range f where
  continuous_toFun := hf.continuous.subtype_mk _
  continuous_invFun := hf.continuous_iff.2 <| by simp [continuous_subtype_val]
  toEquiv := Equiv.ofInjective f hf.injective

@[deprecated (since := "2024-10-26")]
alias ofEmbedding := ofIsEmbedding

protected theorem secondCountableTopology [SecondCountableTopology Y]
    (h : X ≃ₜ Y) : SecondCountableTopology X :=
  h.isInducing.secondCountableTopology

/-- If `h : X → Y` is a homeomorphism, `h(s)` is compact iff `s` is. -/
@[simp]
theorem isCompact_image {s : Set X} (h : X ≃ₜ Y) : IsCompact (h '' s) ↔ IsCompact s :=
  h.isEmbedding.isCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is compact iff `s` is. -/
@[simp]
theorem isCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm]; exact h.symm.isCompact_image

/-- If `h : X → Y` is a homeomorphism, `s` is σ-compact iff `h(s)` is. -/
@[simp]
theorem isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) :
    IsSigmaCompact (h '' s) ↔ IsSigmaCompact s :=
  h.isEmbedding.isSigmaCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is σ-compact iff `s` is. -/
@[simp]
theorem isSigmaCompact_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsSigmaCompact (h ⁻¹' s) ↔ IsSigmaCompact s := by
  rw [← image_symm]; exact h.symm.isSigmaCompact_image

@[simp]
theorem isPreconnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPreconnected (h '' s) ↔ IsPreconnected s :=
  ⟨fun hs ↦ by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs ↦ hs.image _ h.continuous.continuousOn⟩

@[simp]
theorem isPreconnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPreconnected (h ⁻¹' s) ↔ IsPreconnected s := by
  rw [← image_symm, isPreconnected_image]

@[simp]
theorem isConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsConnected (h '' s) ↔ IsConnected s :=
  image_nonempty.and h.isPreconnected_image

@[simp]
theorem isConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsConnected (h ⁻¹' s) ↔ IsConnected s := by
  rw [← image_symm, isConnected_image]

theorem image_connectedComponentIn {s : Set X} (h : X ≃ₜ Y) {x : X} (hx : x ∈ s) :
    h '' connectedComponentIn s x = connectedComponentIn (h '' s) (h x) := by
  refine (h.continuous.image_connectedComponentIn_subset hx).antisymm ?_
  have := h.symm.continuous.image_connectedComponentIn_subset (mem_image_of_mem h hx)
  rwa [image_subset_iff, h.preimage_symm, h.image_symm, h.preimage_image, h.symm_apply_apply]
    at this

@[simp]
theorem comap_cocompact (h : X ≃ₜ Y) : comap h (cocompact Y) = cocompact X :=
  (comap_cocompact_le h.continuous).antisymm <|
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩

@[simp]
theorem map_cocompact (h : X ≃ₜ Y) : map h (cocompact X) = cocompact Y := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]

protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ

protected theorem t0Space [T0Space X] (h : X ≃ₜ Y) : T0Space Y := h.symm.isEmbedding.t0Space
protected theorem t1Space [T1Space X] (h : X ≃ₜ Y) : T1Space Y := h.symm.isEmbedding.t1Space
protected theorem t2Space [T2Space X] (h : X ≃ₜ Y) : T2Space Y := h.symm.isEmbedding.t2Space
protected theorem t25Space [T25Space X] (h : X ≃ₜ Y) : T25Space Y := h.symm.isEmbedding.t25Space
protected theorem t3Space [T3Space X] (h : X ≃ₜ Y) : T3Space Y := h.symm.isEmbedding.t3Space

theorem isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbedding h :=
  { h.isEmbedding with dense := h.surjective.denseRange }

protected lemma totallyDisconnectedSpace (h : X ≃ₜ Y) [tdc : TotallyDisconnectedSpace X] :
    TotallyDisconnectedSpace Y :=
  (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[deprecated (since := "2024-09-30")]
alias denseEmbedding := isDenseEmbedding

protected theorem normalSpace [NormalSpace X] (h : X ≃ₜ Y) : NormalSpace Y :=
  h.symm.isClosedEmbedding.normalSpace

protected theorem t4Space [T4Space X] (h : X ≃ₜ Y) : T4Space Y := h.symm.isClosedEmbedding.t4Space
protected theorem t5Space [T5Space X] (h : X ≃ₜ Y) : T5Space Y := h.symm.isClosedEmbedding.t5Space

@[simp]
theorem map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) = 𝓝 (h x) :=
  h.isEmbedding.map_nhds_of_mem _ (by simp)

@[simp]
theorem map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[≠] x) = 𝓝[≠] (h x) := by
  convert h.isEmbedding.map_nhdsWithin_eq ({x}ᶜ) x
  rw [h.image_compl, Set.image_singleton]

theorem symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]

theorem nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.isInducing.nhds_eq_comap x

@[simp]
theorem comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]

@[simp]
theorem comap_coclosedCompact (h : X ≃ₜ Y) : comap h (coclosedCompact Y) = coclosedCompact X :=
  (hasBasis_coclosedCompact.comap h).eq_of_same_basis <| by
    simpa [comp_def] using hasBasis_coclosedCompact.comp_surjective h.injective.preimage_surjective

@[simp]
theorem map_coclosedCompact (h : X ≃ₜ Y) : map h (coclosedCompact X) = coclosedCompact Y := by
  rw [← h.comap_coclosedCompact, map_comap_of_surjective h.surjective]

/-- If the codomain of a homeomorphism is a locally connected space, then the domain is also
a locally connected space. -/
theorem locallyConnectedSpace [i : LocallyConnectedSpace Y] (h : X ≃ₜ Y) :
    LocallyConnectedSpace X := by
  have : ∀ x, (𝓝 x).HasBasis (fun s ↦ IsOpen s ∧ h x ∈ s ∧ IsConnected s)
      (h.symm '' ·) := fun x ↦ by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs ↦ ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuousOn

/-- The codomain of a homeomorphism is a locally compact space if and only if
the domain is a locally compact space. -/
theorem locallyCompactSpace_iff (h : X ≃ₜ Y) :
    LocallyCompactSpace X ↔ LocallyCompactSpace Y := by
  exact ⟨fun _ => h.symm.isOpenEmbedding.locallyCompactSpace,
    fun _ => h.isClosedEmbedding.locallyCompactSpace⟩

@[simp]
theorem comp_continuousOn_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.isInducing.continuousOn_iff.symm

theorem comp_continuousWithinAt_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) (z : Z) :
    ContinuousWithinAt f s z ↔ ContinuousWithinAt (h ∘ f) s z :=
  h.isInducing.continuousWithinAt_iff

/-- A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between subtypes corresponding to
predicates `p : X → Prop` and `q : Y → Prop` so long as `p = q ∘ h`. -/
@[simps!]
def subtype {p : X → Prop} {q : Y → Prop} (h : X ≃ₜ Y) (h_iff : ∀ x, p x ↔ q (h x)) :
    {x // p x} ≃ₜ {y // q y} where
  continuous_toFun := by simpa [Equiv.coe_subtypeEquiv_eq_map] using h.continuous.subtype_map _
  continuous_invFun := by simpa [Equiv.coe_subtypeEquiv_eq_map] using
    h.symm.continuous.subtype_map _
  __ := h.subtypeEquiv h_iff

@[simp]
lemma subtype_toEquiv {p : X → Prop} {q : Y → Prop} (h : X ≃ₜ Y) (h_iff : ∀ x, p x ↔ q (h x)) :
    (h.subtype h_iff).toEquiv = h.toEquiv.subtypeEquiv h_iff :=
  rfl

/-- A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between sets `s : Set X` and `t : Set Y`
whenever `h` maps `s` onto `t`. -/
abbrev sets {s : Set X} {t : Set Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t) : s ≃ₜ t :=
  h.subtype <| Set.ext_iff.mp h_eq

/-- If two sets are equal, then they are homeomorphic. -/
def setCongr {s t : Set X} (h : s = t) : s ≃ₜ t where
  continuous_toFun := continuous_inclusion h.subset
  continuous_invFun := continuous_inclusion h.symm.subset
  toEquiv := Equiv.setCongr h

section

variable {ι : Type*}

/-- The topological space `Π i, Y i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not. -/
@[simps!]
def piEquivPiSubtypeProd (p : ι → Prop) (Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
    [DecidablePred p] : (∀ i, Y i) ≃ₜ (∀ i : { x // p x }, Y i) × ∀ i : { x // ¬p x }, Y i where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  continuous_toFun := by
    apply Continuous.prodMk <;> exact continuous_pi fun j => continuous_apply j.1
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]

variable [DecidableEq ι] (i : ι)

/-- A product of topological spaces can be split as the binary product of one of the spaces and
  the product of all the remaining spaces. -/
@[simps!]
def piSplitAt (Y : ι → Type*) [∀ j, TopologicalSpace (Y j)] :
    (∀ j, Y j) ≃ₜ Y i × ∀ j : { j // j ≠ i }, Y j where
  toEquiv := Equiv.piSplitAt i Y
  continuous_toFun := (continuous_apply i).prodMk (continuous_pi fun j => continuous_apply j.1)
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd

variable (Y)

/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps!]
def funSplitAt : (ι → Y) ≃ₜ Y × ({ j // j ≠ i } → Y) :=
  piSplitAt i _

end

end Homeomorph

namespace Continuous

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace X] [T2Space Y] {f : X ≃ Y}
    (hf : Continuous f) : Continuous f.symm := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage] at hC'

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv]
def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }

end Continuous
