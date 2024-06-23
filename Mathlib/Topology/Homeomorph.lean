/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Support
import Mathlib.Topology.Connected.LocallyConnected

#align_import topology.homeomorph from "leanprover-community/mathlib"@"4c3e1721c58ef9087bbc2c8c38b540f70eda2e53"

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `Homeomorph X Y`: The type of homeomorphisms from `X` to `Y`.
  This type can be denoted using the following notation: `X ≃ₜ Y`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `Equiv.toHomeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.

-/

open Set Filter

open Topology

variable {X : Type*} {Y : Type*} {Z : Type*}

-- not all spaces are homeomorphic to each other
/-- Homeomorphism between `X` and `Y`, also called topological isomorphism -/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by continuity
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by continuity
#align homeomorph Homeomorph

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

theorem toEquiv_injective : Function.Injective (toEquiv : X ≃ₜ Y → X ≃ Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
#align homeomorph.to_equiv_injective Homeomorph.toEquiv_injective

instance : EquivLike (X ≃ₜ Y) X Y where
  coe := fun h => h.toEquiv
  inv := fun h => h.toEquiv.symm
  left_inv := fun h => h.left_inv
  right_inv := fun h => h.right_inv
  coe_injective' := fun _ _ H _ => toEquiv_injective <| DFunLike.ext' H

instance : CoeFun (X ≃ₜ Y) fun _ ↦ X → Y := ⟨DFunLike.coe⟩

@[simp] theorem homeomorph_mk_coe (a : X ≃ Y) (b c) : (Homeomorph.mk a b c : X → Y) = a :=
  rfl
#align homeomorph.homeomorph_mk_coe Homeomorph.homeomorph_mk_coe

/-- The unique homeomorphism between two empty types. -/
protected def empty [IsEmpty X] [IsEmpty Y] : X ≃ₜ Y where
  __ := Equiv.equivOfIsEmpty X Y

/-- Inverse of a homeomorphism. -/
@[symm]
protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
#align homeomorph.symm Homeomorph.symm

@[simp] theorem symm_symm (h : X ≃ₜ Y) : h.symm.symm = h := rfl
#align homeomorph.symm_symm Homeomorph.symm_symm

theorem symm_bijective : Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) → Y ≃ₜ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : X ≃ₜ Y) : Y → X :=
  h.symm
#align homeomorph.simps.symm_apply Homeomorph.Simps.symm_apply

initialize_simps_projections Homeomorph (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv = h :=
  rfl
#align homeomorph.coe_to_equiv Homeomorph.coe_toEquiv

@[simp]
theorem coe_symm_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align homeomorph.coe_symm_to_equiv Homeomorph.coe_symm_toEquiv

@[ext]
theorem ext {h h' : X ≃ₜ Y} (H : ∀ x, h x = h' x) : h = h' :=
  DFunLike.ext _ _ H
#align homeomorph.ext Homeomorph.ext

/-- Identity map as a homeomorphism. -/
@[simps! (config := .asFn) apply]
protected def refl (X : Type*) [TopologicalSpace X] : X ≃ₜ X where
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  toEquiv := Equiv.refl X
#align homeomorph.refl Homeomorph.refl

/-- Composition of two homeomorphisms. -/
@[trans]
protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align homeomorph.trans Homeomorph.trans

@[simp]
theorem trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl
#align homeomorph.trans_apply Homeomorph.trans_apply

@[simp]
theorem symm_trans_apply (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z) :
    (f.trans g).symm z = f.symm (g.symm z) := rfl

@[simp]
theorem homeomorph_mk_coe_symm (a : X ≃ Y) (b c) :
    ((Homeomorph.mk a b c).symm : Y → X) = a.symm :=
  rfl
#align homeomorph.homeomorph_mk_coe_symm Homeomorph.homeomorph_mk_coe_symm

@[simp]
theorem refl_symm : (Homeomorph.refl X).symm = Homeomorph.refl X :=
  rfl
#align homeomorph.refl_symm Homeomorph.refl_symm

@[continuity]
protected theorem continuous (h : X ≃ₜ Y) : Continuous h :=
  h.continuous_toFun
#align homeomorph.continuous Homeomorph.continuous

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : X ≃ₜ Y) : Continuous h.symm :=
  h.continuous_invFun
#align homeomorph.continuous_symm Homeomorph.continuous_symm

@[simp]
theorem apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y
#align homeomorph.apply_symm_apply Homeomorph.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align homeomorph.symm_apply_apply Homeomorph.symm_apply_apply

@[simp]
theorem self_trans_symm (h : X ≃ₜ Y) : h.trans h.symm = Homeomorph.refl X := by
  ext
  apply symm_apply_apply
#align homeomorph.self_trans_symm Homeomorph.self_trans_symm

@[simp]
theorem symm_trans_self (h : X ≃ₜ Y) : h.symm.trans h = Homeomorph.refl Y := by
  ext
  apply apply_symm_apply
#align homeomorph.symm_trans_self Homeomorph.symm_trans_self

protected theorem bijective (h : X ≃ₜ Y) : Function.Bijective h :=
  h.toEquiv.bijective
#align homeomorph.bijective Homeomorph.bijective

protected theorem injective (h : X ≃ₜ Y) : Function.Injective h :=
  h.toEquiv.injective
#align homeomorph.injective Homeomorph.injective

protected theorem surjective (h : X ≃ₜ Y) : Function.Surjective h :=
  h.toEquiv.surjective
#align homeomorph.surjective Homeomorph.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : X ≃ₜ Y) (g : Y → X) (hg : Function.RightInverse g f) : X ≃ₜ Y :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert f.symm.continuous }
#align homeomorph.change_inv Homeomorph.changeInv

@[simp]
theorem symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id :=
  funext h.symm_apply_apply
#align homeomorph.symm_comp_self Homeomorph.symm_comp_self

@[simp]
theorem self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id :=
  funext h.apply_symm_apply
#align homeomorph.self_comp_symm Homeomorph.self_comp_symm

@[simp]
theorem range_coe (h : X ≃ₜ Y) : range h = univ :=
  h.surjective.range_eq
#align homeomorph.range_coe Homeomorph.range_coe

theorem image_symm (h : X ≃ₜ Y) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage
#align homeomorph.image_symm Homeomorph.image_symm

theorem preimage_symm (h : X ≃ₜ Y) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm
#align homeomorph.preimage_symm Homeomorph.preimage_symm

@[simp]
theorem image_preimage (h : X ≃ₜ Y) (s : Set Y) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s
#align homeomorph.image_preimage Homeomorph.image_preimage

@[simp]
theorem preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s
#align homeomorph.preimage_image Homeomorph.preimage_image

lemma image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ) = (h '' s)ᶜ :=
  h.toEquiv.image_compl s

protected theorem inducing (h : X ≃ₜ Y) : Inducing h :=
  inducing_of_inducing_compose h.continuous h.symm.continuous <| by
    simp only [symm_comp_self, inducing_id]
#align homeomorph.inducing Homeomorph.inducing

theorem induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.inducing.1.symm
#align homeomorph.induced_eq Homeomorph.induced_eq

protected theorem quotientMap (h : X ≃ₜ Y) : QuotientMap h :=
  QuotientMap.of_quotientMap_compose h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, QuotientMap.id]
#align homeomorph.quotient_map Homeomorph.quotientMap

theorem coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.quotientMap.2.symm
#align homeomorph.coinduced_eq Homeomorph.coinduced_eq

protected theorem embedding (h : X ≃ₜ Y) : Embedding h :=
  ⟨h.inducing, h.injective⟩
#align homeomorph.embedding Homeomorph.embedding

protected theorem secondCountableTopology [SecondCountableTopology Y]
    (h : X ≃ₜ Y) : SecondCountableTopology X :=
  h.inducing.secondCountableTopology
#align homeomorph.second_countable_topology Homeomorph.secondCountableTopology

/-- If `h : X → Y` is a homeomorphism, `h(s)` is compact iff `s` is. -/
@[simp]
theorem isCompact_image {s : Set X} (h : X ≃ₜ Y) : IsCompact (h '' s) ↔ IsCompact s :=
  h.embedding.isCompact_iff.symm
#align homeomorph.is_compact_image Homeomorph.isCompact_image

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is compact iff `s` is. -/
@[simp]
theorem isCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm]; exact h.symm.isCompact_image
#align homeomorph.is_compact_preimage Homeomorph.isCompact_preimage

/-- If `h : X → Y` is a homeomorphism, `s` is σ-compact iff `h(s)` is. -/
@[simp]
theorem isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) :
    IsSigmaCompact (h '' s) ↔ IsSigmaCompact s :=
  h.embedding.isSigmaCompact_iff.symm

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
#align homeomorph.comap_cocompact Homeomorph.comap_cocompact

@[simp]
theorem map_cocompact (h : X ≃ₜ Y) : map h (cocompact X) = cocompact Y := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]
#align homeomorph.map_cocompact Homeomorph.map_cocompact

protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ
#align homeomorph.compact_space Homeomorph.compactSpace

protected theorem t0Space [T0Space X] (h : X ≃ₜ Y) : T0Space Y :=
  h.symm.embedding.t0Space
#align homeomorph.t0_space Homeomorph.t0Space

protected theorem t1Space [T1Space X] (h : X ≃ₜ Y) : T1Space Y :=
  h.symm.embedding.t1Space
#align homeomorph.t1_space Homeomorph.t1Space

protected theorem t2Space [T2Space X] (h : X ≃ₜ Y) : T2Space Y :=
  h.symm.embedding.t2Space
#align homeomorph.t2_space Homeomorph.t2Space

protected theorem t3Space [T3Space X] (h : X ≃ₜ Y) : T3Space Y :=
  h.symm.embedding.t3Space
#align homeomorph.t3_space Homeomorph.t3Space

protected theorem denseEmbedding (h : X ≃ₜ Y) : DenseEmbedding h :=
  { h.embedding with dense := h.surjective.denseRange }
#align homeomorph.dense_embedding Homeomorph.denseEmbedding

@[simp]
theorem isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.quotientMap.isOpen_preimage
#align homeomorph.is_open_preimage Homeomorph.isOpen_preimage

@[simp]
theorem isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, isOpen_preimage]
#align homeomorph.is_open_image Homeomorph.isOpen_image

protected theorem isOpenMap (h : X ≃ₜ Y) : IsOpenMap h := fun _ => h.isOpen_image.2
#align homeomorph.is_open_map Homeomorph.isOpenMap

@[simp]
theorem isClosed_preimage (h : X ≃ₜ Y) {s : Set Y} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]
#align homeomorph.is_closed_preimage Homeomorph.isClosed_preimage

@[simp]
theorem isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, isClosed_preimage]
#align homeomorph.is_closed_image Homeomorph.isClosed_image

protected theorem isClosedMap (h : X ≃ₜ Y) : IsClosedMap h := fun _ => h.isClosed_image.2
#align homeomorph.is_closed_map Homeomorph.isClosedMap

protected theorem openEmbedding (h : X ≃ₜ Y) : OpenEmbedding h :=
  openEmbedding_of_embedding_open h.embedding h.isOpenMap
#align homeomorph.open_embedding Homeomorph.openEmbedding

protected theorem closedEmbedding (h : X ≃ₜ Y) : ClosedEmbedding h :=
  closedEmbedding_of_embedding_closed h.embedding h.isClosedMap
#align homeomorph.closed_embedding Homeomorph.closedEmbedding

protected theorem normalSpace [NormalSpace X] (h : X ≃ₜ Y) : NormalSpace Y :=
  h.symm.closedEmbedding.normalSpace

protected theorem t4Space [T4Space X] (h : X ≃ₜ Y) : T4Space Y :=
  h.symm.closedEmbedding.t4Space
#align homeomorph.normal_space Homeomorph.t4Space

theorem preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _
#align homeomorph.preimage_closure Homeomorph.preimage_closure

theorem image_closure (h : X ≃ₜ Y) (s : Set X) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]
#align homeomorph.image_closure Homeomorph.image_closure

theorem preimage_interior (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _
#align homeomorph.preimage_interior Homeomorph.preimage_interior

theorem image_interior (h : X ≃ₜ Y) (s : Set X) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]
#align homeomorph.image_interior Homeomorph.image_interior

theorem preimage_frontier (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _
#align homeomorph.preimage_frontier Homeomorph.preimage_frontier

theorem image_frontier (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm, preimage_frontier]
#align homeomorph.image_frontier Homeomorph.image_frontier

@[to_additive]
theorem _root_.HasCompactMulSupport.comp_homeomorph {M} [One M] {f : Y → M}
    (hf : HasCompactMulSupport f) (φ : X ≃ₜ Y) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_closedEmbedding φ.closedEmbedding
#align has_compact_mul_support.comp_homeomorph HasCompactMulSupport.comp_homeomorph
#align has_compact_support.comp_homeomorph HasCompactSupport.comp_homeomorph

@[simp]
theorem map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) = 𝓝 (h x) :=
  h.embedding.map_nhds_of_mem _ (by simp)
#align homeomorph.map_nhds_eq Homeomorph.map_nhds_eq

@[simp]
theorem map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[≠] x) = 𝓝[≠] (h x) := by
  convert h.embedding.map_nhdsWithin_eq ({x}ᶜ) x
  rw [h.image_compl, Set.image_singleton]

theorem symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]
#align homeomorph.symm_map_nhds_eq Homeomorph.symm_map_nhds_eq

theorem nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.inducing.nhds_eq_comap x
#align homeomorph.nhds_eq_comap Homeomorph.nhds_eq_comap

@[simp]
theorem comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]
#align homeomorph.comap_nhds_eq Homeomorph.comap_nhds_eq

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
  exact ⟨fun _ => h.symm.openEmbedding.locallyCompactSpace,
    fun _ => h.closedEmbedding.locallyCompactSpace⟩

/-- An equiv between topological spaces respecting openness is a homeomorphism. -/
@[simps toEquiv]
def _root_.Equiv.toHomeomorph (e : X ≃ Y) (he : ∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : X ≃ₜ Y where
  toEquiv := e
  continuous_toFun := continuous_def.2 fun s ↦ (he _).2
  continuous_invFun := continuous_def.2 fun s ↦ by convert (he _).1; simp

@[simp] lemma _root_.Equiv.coe_toHomeomorph (e : X ≃ Y) (he) : ⇑(e.toHomeomorph he) = e := rfl
lemma toHomeomorph_apply (e : X ≃ Y) (he) (x : X) : e.toHomeomorph he x = e x := rfl

@[simp] lemma _root_.Equiv.toHomeomorph_refl :
  (Equiv.refl X).toHomeomorph (fun _s ↦ Iff.rfl) = Homeomorph.refl _ := rfl

@[simp] lemma _root_.Equiv.toHomeomorph_symm (e : X ≃ Y) (he) :
  (e.toHomeomorph he).symm = e.symm.toHomeomorph fun s ↦ by convert (he _).symm; simp := rfl

lemma _root_.Equiv.toHomeomorph_trans (e : X ≃ Y) (f : Y ≃ Z) (he hf) :
    (e.trans f).toHomeomorph (fun _s ↦ (he _).trans (hf _)) =
    (e.toHomeomorph he).trans (f.toHomeomorph hf) := rfl

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps]
def _root_.Equiv.toHomeomorphOfInducing (f : X ≃ Y) (hf : Inducing f) : X ≃ₜ Y :=
  { f with
    toFun := f
    invFun := f.symm
    continuous_toFun := hf.continuous
    continuous_invFun := hf.continuous_iff.2 <| by simpa using continuous_id }
#align equiv.to_homeomorph_of_inducing Equiv.toHomeomorphOfInducing

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps!]
def _root_.Equiv.toHomeomorphOfContinuousOpen (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    X ≃ₜ Y :=
  e.toHomeomorphOfInducing <|
    openEmbedding_of_continuous_injective_open h₁ e.injective h₂ |>.toInducing
#align homeomorph.homeomorph_of_continuous_open Equiv.toHomeomorphOfContinuousOpen

@[deprecated] -- May 20th 2024
alias homeomorphOfContinuousOpen := _root_.Equiv.toHomeomorphOfContinuousOpen

/-- An embedding is an homeomorphism onto its range. -/
@[simps! apply_coe]
noncomputable def _root_.Embedding.toHomeomorph {f : X → Y} (hf : Embedding f) :
    X ≃ₜ Set.range f :=
  Equiv.ofInjective f hf.inj |>.toHomeomorphOfInducing <|
    inducing_subtype_val.of_comp_iff.mp hf.toInducing
#align homeomorph.of_embedding Embedding.toHomeomorph

@[deprecated] -- May 20th 2024
alias ofEmbedding := _root_.Embedding.toHomeomorph

/-- A surjective embedding is a homeomorphism. -/
@[simps! apply]
noncomputable def _root_.Embedding.toHomeomorphOfSurjective {f : X → Y}  (hf : Embedding f)
    (hsurj : Function.Surjective f) : X ≃ₜ Y :=
  Equiv.ofBijective f ⟨hf.inj, hsurj⟩ |>.toHomeomorphOfInducing hf.toInducing

@[deprecated] -- May 20th 2024
alias _root_.Embedding.toHomeomeomorph_of_surjective := Embedding.toHomeomorphOfSurjective

@[simp]
theorem comp_continuousOn_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.inducing.continuousOn_iff.symm
#align homeomorph.comp_continuous_on_iff Homeomorph.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff (h : X ≃ₜ Y) {f : Z → X} : Continuous (h ∘ f) ↔ Continuous f :=
  h.inducing.continuous_iff.symm
#align homeomorph.comp_continuous_iff Homeomorph.comp_continuous_iff

@[simp]
theorem comp_continuous_iff' (h : X ≃ₜ Y) {f : Y → Z} : Continuous (f ∘ h) ↔ Continuous f :=
  h.quotientMap.continuous_iff.symm
#align homeomorph.comp_continuous_iff' Homeomorph.comp_continuous_iff'

theorem comp_continuousAt_iff (h : X ≃ₜ Y) (f : Z → X) (z : Z) :
    ContinuousAt (h ∘ f) z ↔ ContinuousAt f z :=
  h.inducing.continuousAt_iff.symm
#align homeomorph.comp_continuous_at_iff Homeomorph.comp_continuousAt_iff

theorem comp_continuousAt_iff' (h : X ≃ₜ Y) (f : Y → Z) (x : X) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.inducing.continuousAt_iff' (by simp)
#align homeomorph.comp_continuous_at_iff' Homeomorph.comp_continuousAt_iff'

theorem comp_continuousWithinAt_iff (h : X ≃ₜ Y) (f : Z → X) (s : Set Z) (z : Z) :
    ContinuousWithinAt f s z ↔ ContinuousWithinAt (h ∘ f) s z :=
  h.inducing.continuousWithinAt_iff
#align homeomorph.comp_continuous_within_at_iff Homeomorph.comp_continuousWithinAt_iff

@[simp]
theorem comp_isOpenMap_iff (h : X ≃ₜ Y) {f : Z → X} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f, ← h.symm_comp_self, Function.comp.assoc]
  exact h.symm.isOpenMap.comp hf
#align homeomorph.comp_is_open_map_iff Homeomorph.comp_isOpenMap_iff

@[simp]
theorem comp_isOpenMap_iff' (h : X ≃ₜ Y) {f : Y → Z} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f, ← h.self_comp_symm, ← Function.comp.assoc]
  exact hf.comp h.symm.isOpenMap
#align homeomorph.comp_is_open_map_iff' Homeomorph.comp_isOpenMap_iff'

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
#align homeomorph.set_congr Homeomorph.setCongr

/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : Sum X Y ≃ₜ Sum X' Y' where
  continuous_toFun := h₁.continuous.sum_map h₂.continuous
  continuous_invFun := h₁.symm.continuous.sum_map h₂.symm.continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv
#align homeomorph.sum_congr Homeomorph.sumCongr

/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where
  continuous_toFun := h₁.continuous.prod_map h₂.continuous
  continuous_invFun := h₁.symm.continuous.prod_map h₂.symm.continuous
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align homeomorph.prod_congr Homeomorph.prodCongr

@[simp]
theorem prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align homeomorph.prod_congr_symm Homeomorph.prodCongr_symm

@[simp]
theorem coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align homeomorph.coe_prod_congr Homeomorph.coe_prodCongr

section

variable (X Y Z)

/-- `X × Y` is homeomorphic to `Y × X`. -/
def prodComm : X × Y ≃ₜ Y × X where
  continuous_toFun := continuous_snd.prod_mk continuous_fst
  continuous_invFun := continuous_snd.prod_mk continuous_fst
  toEquiv := Equiv.prodComm X Y
#align homeomorph.prod_comm Homeomorph.prodComm

@[simp]
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  rfl
#align homeomorph.prod_comm_symm Homeomorph.prodComm_symm

@[simp]
theorem coe_prodComm : ⇑(prodComm X Y) = Prod.swap :=
  rfl
#align homeomorph.coe_prod_comm Homeomorph.coe_prodComm

/-- `(X × Y) × Z` is homeomorphic to `X × (Y × Z)`. -/
def prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where
  continuous_toFun := continuous_fst.fst.prod_mk (continuous_fst.snd.prod_mk continuous_snd)
  continuous_invFun := (continuous_fst.prod_mk continuous_snd.fst).prod_mk continuous_snd.snd
  toEquiv := Equiv.prodAssoc X Y Z
#align homeomorph.prod_assoc Homeomorph.prodAssoc

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! (config := .asFn) apply]
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prod_mk continuous_const
#align homeomorph.prod_punit Homeomorph.prodPUnit

/-- `{*} × X` is homeomorphic to `X`. -/
def punitProd : PUnit × X ≃ₜ X :=
  (prodComm _ _).trans (prodPUnit _)
#align homeomorph.punit_prod Homeomorph.punitProd

@[simp] theorem coe_punitProd : ⇑(punitProd X) = Prod.snd := rfl
#align homeomorph.coe_punit_prod Homeomorph.coe_punitProd

/-- If both `X` and `Y` have a unique element, then `X ≃ₜ Y`. -/
@[simps!]
def homeomorphOfUnique [Unique X] [Unique Y] : X ≃ₜ Y :=
  { Equiv.equivOfUnique X Y with
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }
#align homeomorph.homeomorph_of_unique Homeomorph.homeomorphOfUnique

end

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps! apply toEquiv]
def piCongrLeft {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ₜ ∀ j, Y j where
  continuous_toFun := continuous_pi <| e.forall_congr_left.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) : (∀ i, Y₁ i) ≃ₜ ∀ i, Y₂ i where
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (F i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (F i).symm.continuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv
#align homeomorph.Pi_congr_right Homeomorph.piCongrRight

@[simp]
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl
#align homeomorph.Pi_congr_right_symm Homeomorph.piCongrRight_symm

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ → Type*} {Y₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (Y₁ i₁)] [∀ i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (∀ i₁, Y₁ i₁) ≃ₜ ∀ i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

-- Porting note (#11215): TODO: align the order of universes with `Equiv.ulift`
/-- `ULift X` is homeomorphic to `X`. -/
def ulift.{u, v} {X : Type u} [TopologicalSpace X] : ULift.{v, u} X ≃ₜ X where
  continuous_toFun := continuous_uLift_down
  continuous_invFun := continuous_uLift_up
  toEquiv := Equiv.ulift
#align homeomorph.ulift Homeomorph.ulift

section Distrib

/-- `(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`. -/
def sumProdDistrib : Sum X Y × Z ≃ₜ Sum (X × Z) (Y × Z) :=
  .symm <|
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
      ((continuous_inl.prod_map continuous_id).sum_elim
        (continuous_inr.prod_map continuous_id)) <|
      (isOpenMap_inl.prod IsOpenMap.id).sum_elim (isOpenMap_inr.prod IsOpenMap.id)
#align homeomorph.sum_prod_distrib Homeomorph.sumProdDistrib

/-- `X × (Y ⊕ Z)` is homeomorphic to `X × Y ⊕ X × Z`. -/
def prodSumDistrib : X × Sum Y Z ≃ₜ Sum (X × Y) (X × Z) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)
#align homeomorph.prod_sum_distrib Homeomorph.prodSumDistrib

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
def sigmaProdDistrib : (Σi, X i) × Y ≃ₜ Σi, X i × Y :=
  .symm <|
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prod_mk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prod IsOpenMap.id)
#align homeomorph.sigma_prod_distrib Homeomorph.sigmaProdDistrib

end Distrib

/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! (config := .asFn)]
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι → X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id
#align homeomorph.fun_unique Homeomorph.funUnique

/-- Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`. -/
@[simps! (config := .asFn)]
def piFinTwo.{u} (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)] : (∀ i, X i) ≃ₜ X 0 × X 1 where
  toEquiv := piFinTwoEquiv X
  continuous_toFun := (continuous_apply 0).prod_mk (continuous_apply 1)
  continuous_invFun := continuous_pi <| Fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩
#align homeomorph.pi_fin_two Homeomorph.piFinTwo

/-- Homeomorphism between `X² = Fin 2 → X` and `X × X`. -/
@[simps! (config := .asFn)]
def finTwoArrow : (Fin 2 → X) ≃ₜ X × X :=
  { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }
#align homeomorph.fin_two_arrow Homeomorph.finTwoArrow

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- Porting note (#11215): TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.restrict_mapsTo (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s
#align homeomorph.image Homeomorph.image

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! (config := .asFn)]
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _
#align homeomorph.set.univ Homeomorph.Set.univ

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prod_mk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prod_mk continuous_subtype_val.snd').subtype_mk _
#align homeomorph.set.prod Homeomorph.Set.prod

section

variable {ι : Type*}

/-- The topological space `Π i, Y i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not. -/
@[simps!]
def piEquivPiSubtypeProd (p : ι → Prop) (Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
    [DecidablePred p] : (∀ i, Y i) ≃ₜ (∀ i : { x // p x }, Y i) × ∀ i : { x // ¬p x }, Y i where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  continuous_toFun := by
    apply Continuous.prod_mk <;> exact continuous_pi fun j => continuous_apply j.1
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
#align homeomorph.pi_equiv_pi_subtype_prod Homeomorph.piEquivPiSubtypeProd

variable [DecidableEq ι] (i : ι)

/-- A product of topological spaces can be split as the binary product of one of the spaces and
  the product of all the remaining spaces. -/
@[simps!]
def piSplitAt (Y : ι → Type*) [∀ j, TopologicalSpace (Y j)] :
    (∀ j, Y j) ≃ₜ Y i × ∀ j : { j // j ≠ i }, Y j where
  toEquiv := Equiv.piSplitAt i Y
  continuous_toFun := (continuous_apply i).prod_mk (continuous_pi fun j => continuous_apply j.1)
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd
#align homeomorph.pi_split_at Homeomorph.piSplitAt

variable (Y)

/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps!]
def funSplitAt : (ι → Y) ≃ₜ Y × ({ j // j ≠ i } → Y) :=
  piSplitAt i _
#align homeomorph.fun_split_at Homeomorph.funSplitAt

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
#align continuous.continuous_symm_of_equiv_compact_to_t2 Continuous.continuous_symm_of_equiv_compact_to_t2

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv] -- Porting note: was `@[simps]`
def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }
#align continuous.homeo_of_equiv_compact_to_t2 Continuous.homeoOfEquivCompactToT2

end Continuous
