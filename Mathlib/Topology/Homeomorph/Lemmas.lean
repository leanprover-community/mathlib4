/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Further properties of homeomorphisms

This file proves further properties of homeomorphisms between topological spaces.
Pretty much every topological property is preserved under homeomorphisms.

-/

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*}

section

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

namespace Homeomorph

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

theorem isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbedding h :=
  { h.isEmbedding with dense := h.surjective.denseRange }

protected lemma totallyDisconnectedSpace (h : X ≃ₜ Y) [tdc : TotallyDisconnectedSpace X] :
    TotallyDisconnectedSpace Y :=
  (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[simp]
theorem map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[≠] x) = 𝓝[≠] (h x) := by
  convert h.isEmbedding.map_nhdsWithin_eq ({x}ᶜ) x
  rw [h.image_compl, Set.image_singleton]

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

section prod

variable (X Y W Z)

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
def prodUnique [Unique Y] :
    X × Y ≃ₜ X where
  toEquiv := Equiv.prodUnique X Y
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

@[simp] theorem coe_prodUnique [Unique Y] : ⇑(prodUnique X Y) = Prod.fst := rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
def uniqueProd (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [Unique X] :
    X × Y ≃ₜ Y :=
  (prodComm _ _).trans (prodUnique Y X)

@[simp] theorem coe_uniqueProd [Unique X] : ⇑(uniqueProd X Y) = Prod.snd := rfl

/-- The product over `S ⊕ T` of a family of topological spaces
is homeomorphic to the product of (the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `Homeomorph`.
-/
def sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  continuous_toFun := .prodMk (by fun_prop) (by fun_prop)
  continuous_invFun := continuous_pi <| by rintro (s | t) <;> simp <;> fun_prop

/-- The product `Π t : α, f t` of a family of topological spaces is homeomorphic to the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
@[simps! -fullyApplied]
def piUnique {α : Type*} [Unique α] (f : α → Type*) [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃ₜ f default :=
  (Equiv.piUnique f).toHomeomorphOfContinuousOpen (continuous_apply default) (isOpenMap_eval _)

end prod

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps +simpRhs toEquiv, simps! -isSimp apply]
def piCongrLeft {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ₜ ∀ j, Y j where
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
lemma piCongrLeft_refl {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (∀ i, X i) :=
  rfl

@[simp]
lemma piCongrLeft_symm_apply {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (Y := Y) e).symm = (· <| e ·) :=
  rfl

@[simp]
lemma piCongrLeft_apply_apply {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') (x : ∀ i, Y (e i)) (i : ι) : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) : (∀ i, Y₁ i) ≃ₜ ∀ i, Y₂ i where
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (F i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (F i).symm.continuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ → Type*} {Y₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (Y₁ i₁)] [∀ i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (∀ i₁, Y₁ i₁) ≃ₜ ∀ i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

/-- `ULift X` is homeomorphic to `X`. -/
def ulift.{u, v} {X : Type v} [TopologicalSpace X] : ULift.{u, v} X ≃ₜ X where
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp
  toEquiv := Equiv.ulift

/-- The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism. -/
@[simps!]
def sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)  where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    dsimp [Equiv.sumArrowEquivProdArrow]
    fun_prop
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

private theorem _root_.Fin.appendEquiv_eq_homeomorph (m n : ℕ) : Fin.appendEquiv m n =
    ((sumArrowHomeomorphProdArrow).symm.trans
    (piCongrLeft (Y := fun _ ↦ X) finSumFinEquiv)).toEquiv := by
  apply Equiv.symm_bijective.injective
  ext x i <;> simp

theorem _root_.Fin.continuous_append (m n : ℕ) :
    Continuous fun (p : (Fin m → X) × (Fin n → X)) ↦ Fin.append p.1 p.2 := by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_homeomorph]
  exact Homeomorph.continuous_toFun _

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) → X`.
`Fin.appendEquiv` as a homeomorphism -/
@[simps!]
def _root_.Fin.appendHomeomorph (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toEquiv := Fin.appendEquiv m n
  continuous_toFun := Fin.continuous_append m n
  continuous_invFun := by
    rw [Fin.appendEquiv_eq_homeomorph]
    exact Homeomorph.continuous_invFun _

@[simp]
theorem _root_.Fin.appendHomeomorph_toEquiv (m n : ℕ) :
    (Fin.appendHomeomorph (X := X) m n).toEquiv = Fin.appendEquiv m n :=
  rfl

section Distrib

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
@[simps! apply symm_apply toEquiv]
def sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y :=
  Homeomorph.symm <|
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

end Distrib

/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι → X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id

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

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.restrict_mapsTo (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prodMk continuous_subtype_val.snd').subtype_mk _

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

namespace Topology.IsEmbedding

/-- Homeomorphism given an embedding. -/
@[simps! apply_coe]
noncomputable def toHomeomorph {f : X → Y} (hf : IsEmbedding f) :
    X ≃ₜ Set.range f :=
  Equiv.ofInjective f hf.injective |>.toHomeomorphOfIsInducing <|
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

@[deprecated (since := "2025-04-16")]
alias _root_.Homeomorph.ofIsEmbedding := toHomeomorph

/-- A surjective embedding is a homeomorphism. -/
@[simps! apply]
noncomputable def toHomeomorphOfSurjective {f : X → Y}
    (hf : IsEmbedding f) (hsurj : Function.Surjective f) : X ≃ₜ Y :=
  Equiv.ofBijective f ⟨hf.injective, hsurj⟩ |>.toHomeomorphOfIsInducing hf.toIsInducing

@[deprecated (since := "2025-04-16")]
alias toHomeomorph_of_surjective := toHomeomorphOfSurjective

/-- A set is homeomorphic to its image under any embedding. -/
noncomputable def homeomorphImage {f : X → Y} (hf : IsEmbedding f) (s : Set X) : s ≃ₜ f '' s :=
  (hf.comp .subtypeVal).toHomeomorph.trans <| .setCongr <| by simp [Set.range_comp]

end Topology.IsEmbedding

end

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

namespace IsHomeomorph
variable (hf : IsHomeomorph f)
include hf

variable (f) in
/-- Bundled homeomorphism constructed from a map that is a homeomorphism. -/
@[simps! toEquiv apply symm_apply]
noncomputable def homeomorph : X ≃ₜ Y where
  continuous_toFun := hf.1
  continuous_invFun := by
    rw [← continuousOn_univ, ← hf.bijective.2.range_eq]
    exact hf.isOpenMap.continuousOn_range_of_leftInverse (leftInverse_surjInv hf.bijective)
  toEquiv := Equiv.ofBijective f hf.bijective

protected lemma isClosedMap : IsClosedMap f := (hf.homeomorph f).isClosedMap
lemma isInducing : IsInducing f := (hf.homeomorph f).isInducing
lemma isQuotientMap : IsQuotientMap f := (hf.homeomorph f).isQuotientMap
lemma isEmbedding : IsEmbedding f := (hf.homeomorph f).isEmbedding
lemma isOpenEmbedding : IsOpenEmbedding f := (hf.homeomorph f).isOpenEmbedding
lemma isClosedEmbedding : IsClosedEmbedding f := (hf.homeomorph f).isClosedEmbedding
lemma isDenseEmbedding : IsDenseEmbedding f := (hf.homeomorph f).isDenseEmbedding

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

/-- A map is a homeomorphism iff it is continuous, closed and bijective. -/
lemma isHomeomorph_iff_continuous_isClosedMap_bijective : IsHomeomorph f ↔
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
