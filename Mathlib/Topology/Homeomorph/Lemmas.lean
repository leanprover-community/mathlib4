/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Constructions

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

private theorem _root_.Fin.appendEquiv_eq_Homeomorph (m n : ℕ) : Fin.appendEquiv m n =
    ((sumArrowHomeomorphProdArrow).symm.trans
    (piCongrLeft (Y := fun _ ↦ X) finSumFinEquiv)).toEquiv := by
  ext ⟨x1, x2⟩ l
  simp only [sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow,
    finSumFinEquiv, Fin.addCases, Fin.appendEquiv, Fin.append, Equiv.coe_fn_mk]
  by_cases h : l < m
  · simp [h]
  · simp [h]

theorem _root_.Fin.continuous_append (m n : ℕ) :
    Continuous fun (p : (Fin m → X) × (Fin n → X)) ↦ Fin.append p.1 p.2 := by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_Homeomorph]
  exact Homeomorph.continuous_toFun _

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) → X`.
`Fin.appendEquiv` as a homeomorphism -/
@[simps!]
def _root_.Fin.appendHomeomorph (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toEquiv := Fin.appendEquiv m n
  continuous_toFun := Fin.continuous_append m n
  continuous_invFun := by
    rw [Fin.appendEquiv_eq_Homeomorph]
    exact Homeomorph.continuous_invFun _

@[simp]
theorem _root_.Fin.appendHomeomorph_toEquiv (m n : ℕ) :
    (Fin.appendHomeomorph (X := X) m n).toEquiv = Fin.appendEquiv m n :=
  rfl

section Distrib

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

end Distrib

/-- Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`. -/
@[simps! -fullyApplied]
def piFinTwo.{u} (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)] : (∀ i, X i) ≃ₜ X 0 × X 1 where
  toEquiv := piFinTwoEquiv X
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := continuous_pi <| Fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩

/-- Homeomorphism between `X² = Fin 2 → X` and `X × X`. -/
@[simps! -fullyApplied]
def finTwoArrow : (Fin 2 → X) ≃ₜ X × X :=
  { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

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

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {W : Type*} [TopologicalSpace W] {f : X → Y}

/-- Predicate saying that `f` is a homeomorphism.

This should be used only when `f` is a concrete function whose continuous inverse is not easy to
write down. Otherwise, `Homeomorph` should be preferred as it bundles the continuous inverse.

Having both `Homeomorph` and `IsHomeomorph` is justified by the fact that so many function
properties are unbundled in the topology part of the library, and by the fact that a homeomorphism
is not merely a continuous bijection, that is `IsHomeomorph f` is not equivalent to
`Continuous f ∧ Bijective f` but to `Continuous f ∧ Bijective f ∧ IsOpenMap f`. -/
structure IsHomeomorph (f : X → Y) : Prop where
  continuous : Continuous f
  isOpenMap : IsOpenMap f
  bijective : Bijective f

protected theorem Homeomorph.isHomeomorph (h : X ≃ₜ Y) : IsHomeomorph h :=
  ⟨h.continuous, h.isOpenMap, h.bijective⟩

namespace IsHomeomorph
variable (hf : IsHomeomorph f)
include hf

protected lemma injective : Function.Injective f := hf.bijective.injective
protected lemma surjective : Function.Surjective f := hf.bijective.surjective

variable (f) in
/-- Bundled homeomorphism constructed from a map that is a homeomorphism. -/
@[simps! toEquiv apply symm_apply]
noncomputable def homeomorph : X ≃ₜ Y where
  continuous_toFun := hf.1
  continuous_invFun := by
    rw [continuous_iff_continuousOn_univ, ← hf.bijective.2.range_eq]
    exact hf.isOpenMap.continuousOn_range_of_leftInverse (leftInverse_surjInv hf.bijective)
  toEquiv := Equiv.ofBijective f hf.bijective

protected lemma isClosedMap : IsClosedMap f := (hf.homeomorph f).isClosedMap
lemma isInducing : IsInducing f := (hf.homeomorph f).isInducing
lemma isQuotientMap : IsQuotientMap f := (hf.homeomorph f).isQuotientMap
lemma isEmbedding : IsEmbedding f := (hf.homeomorph f).isEmbedding
lemma isOpenEmbedding : IsOpenEmbedding f := (hf.homeomorph f).isOpenEmbedding
lemma isClosedEmbedding : IsClosedEmbedding f := (hf.homeomorph f).isClosedEmbedding
lemma isDenseEmbedding : IsDenseEmbedding f := (hf.homeomorph f).isDenseEmbedding

@[deprecated (since := "2024-10-28")] alias inducing := isInducing

@[deprecated (since := "2024-10-26")]
alias embedding := isEmbedding

@[deprecated (since := "2024-10-22")]
alias quotientMap := isQuotientMap

@[deprecated (since := "2024-10-20")] alias closedEmbedding := isClosedEmbedding
@[deprecated (since := "2024-10-18")]
alias openEmbedding := isOpenEmbedding

@[deprecated (since := "2024-09-30")]
alias denseEmbedding := isDenseEmbedding

end IsHomeomorph

/-- A map is a homeomorphism iff it is the map underlying a bundled homeomorphism `h : X ≃ₜ Y`. -/
lemma isHomeomorph_iff_exists_homeomorph : IsHomeomorph f ↔ ∃ h : X ≃ₜ Y, h = f :=
  ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

/-- A map is a homeomorphism iff it is continuous and has a continuous inverse. -/
lemma isHomeomorph_iff_exists_inverse : IsHomeomorph f ↔ Continuous f ∧ ∃ g : Y → X,
    LeftInverse g f ∧ RightInverse g f ∧ Continuous g := by
  refine ⟨fun hf ↦ ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ ↦ ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

/-- A map is a homeomorphism iff it is a surjective embedding. -/
lemma isHomeomorph_iff_isEmbedding_surjective : IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where
  mp hf := ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

@[deprecated (since := "2024-10-26")]
alias isHomeomorph_iff_embedding_surjective := isHomeomorph_iff_isEmbedding_surjective

/-- A map is a homeomorphism iff it is continuous, closed and bijective. -/
lemma isHomeomorph_iff_continuous_isClosedMap_bijective  : IsHomeomorph f ↔
    Continuous f ∧ IsClosedMap f ∧ Function.Bijective f :=
  ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

/-- A map from a compact space to a T2 space is a homeomorphism iff it is continuous and
  bijective. -/
lemma isHomeomorph_iff_continuous_bijective [CompactSpace X] [T2Space Y] :
    IsHomeomorph f ↔ Continuous f ∧ Bijective f := by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf ↦ ?_
  rw [eq_true hf.isClosedMap, true_and]

protected lemma IsHomeomorph.id : IsHomeomorph (@id X) := ⟨continuous_id, .id, bijective_id⟩

lemma IsHomeomorph.comp {g : Y → Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) :
    IsHomeomorph (g ∘ f) := ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩

lemma IsHomeomorph.sumMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Sum.map f g) := ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩

lemma IsHomeomorph.prodMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Prod.map f g) := ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩

lemma IsHomeomorph.sigmaMap {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] {f : ι → κ}
    (hf : Bijective f) {g : (i : ι) → X i → Y (f i)} (hg : ∀ i, IsHomeomorph (g i)) :
    IsHomeomorph (Sigma.map f g) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective,] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i ↦ (hg i).1, hf.2.sigma_map fun i ↦ (hg i).2⟩

lemma IsHomeomorph.pi_map {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsHomeomorph (f i)) :
    IsHomeomorph (fun (x : ∀ i, X i) i ↦ f i (x i)) :=
  (Homeomorph.piCongrRight fun i ↦ (h i).homeomorph (f i)).isHomeomorph
