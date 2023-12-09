/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Support

#align_import topology.homeomorph from "leanprover-community/mathlib"@"4c3e1721c58ef9087bbc2c8c38b540f70eda2e53"

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `Homeomorph α β`: The type of homeomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ₜ β`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `Homeomorph.homeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.

-/

open Set Filter

open Topology

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

-- not all spaces are homeomorphic to each other
/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
structure Homeomorph (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    extends α ≃ β where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by continuity
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by continuity
#align homeomorph Homeomorph

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ₜ β → α ≃ β)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
#align homeomorph.to_equiv_injective Homeomorph.toEquiv_injective

instance : EquivLike (α ≃ₜ β) α β where
  coe := fun h => h.toEquiv
  inv := fun h => h.toEquiv.symm
  left_inv := fun h => h.left_inv
  right_inv := fun h => h.right_inv
  coe_injective' := fun _ _ H _ => toEquiv_injective <| FunLike.ext' H

instance : CoeFun (α ≃ₜ β) fun _ ↦ α → β := ⟨FunLike.coe⟩

@[simp]
theorem homeomorph_mk_coe (a : Equiv α β) (b c) : (Homeomorph.mk a b c : α → β) = a :=
  rfl
#align homeomorph.homeomorph_mk_coe Homeomorph.homeomorph_mk_coe

/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
#align homeomorph.symm Homeomorph.symm

@[simp] theorem symm_symm (h : α ≃ₜ β) : h.symm.symm = h := rfl
#align homeomorph.symm_symm Homeomorph.symm_symm

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ₜ β) : β → α :=
  h.symm
#align homeomorph.simps.symm_apply Homeomorph.Simps.symm_apply

initialize_simps_projections Homeomorph (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toEquiv (h : α ≃ₜ β) : ⇑h.toEquiv = h :=
  rfl
#align homeomorph.coe_to_equiv Homeomorph.coe_toEquiv

@[simp]
theorem coe_symm_toEquiv (h : α ≃ₜ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align homeomorph.coe_symm_to_equiv Homeomorph.coe_symm_toEquiv

@[ext]
theorem ext {h h' : α ≃ₜ β} (H : ∀ x, h x = h' x) : h = h' :=
  FunLike.ext _ _ H
#align homeomorph.ext Homeomorph.ext

/-- Identity map as a homeomorphism. -/
@[simps! (config := { fullyApplied := false }) apply]
protected def refl (α : Type*) [TopologicalSpace α] : α ≃ₜ α where
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  toEquiv := Equiv.refl α
#align homeomorph.refl Homeomorph.refl

/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align homeomorph.trans Homeomorph.trans

@[simp]
theorem trans_apply (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl
#align homeomorph.trans_apply Homeomorph.trans_apply

@[simp] theorem symm_trans_apply (f : α ≃ₜ β) (g : β ≃ₜ γ) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

@[simp]
theorem homeomorph_mk_coe_symm (a : Equiv α β) (b c) :
    ((Homeomorph.mk a b c).symm : β → α) = a.symm :=
  rfl
#align homeomorph.homeomorph_mk_coe_symm Homeomorph.homeomorph_mk_coe_symm

@[simp]
theorem refl_symm : (Homeomorph.refl α).symm = Homeomorph.refl α :=
  rfl
#align homeomorph.refl_symm Homeomorph.refl_symm

@[continuity]
protected theorem continuous (h : α ≃ₜ β) : Continuous h :=
  h.continuous_toFun
#align homeomorph.continuous Homeomorph.continuous

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ₜ β) : Continuous h.symm :=
  h.continuous_invFun
#align homeomorph.continuous_symm Homeomorph.continuous_symm

@[simp]
theorem apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x
#align homeomorph.apply_symm_apply Homeomorph.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align homeomorph.symm_apply_apply Homeomorph.symm_apply_apply

@[simp]
theorem self_trans_symm (h : α ≃ₜ β) : h.trans h.symm = Homeomorph.refl α := by
  ext
  apply symm_apply_apply
#align homeomorph.self_trans_symm Homeomorph.self_trans_symm

@[simp]
theorem symm_trans_self (h : α ≃ₜ β) : h.symm.trans h = Homeomorph.refl β := by
  ext
  apply apply_symm_apply
#align homeomorph.symm_trans_self Homeomorph.symm_trans_self

protected theorem bijective (h : α ≃ₜ β) : Function.Bijective h :=
  h.toEquiv.bijective
#align homeomorph.bijective Homeomorph.bijective

protected theorem injective (h : α ≃ₜ β) : Function.Injective h :=
  h.toEquiv.injective
#align homeomorph.injective Homeomorph.injective

protected theorem surjective (h : α ≃ₜ β) : Function.Surjective h :=
  h.toEquiv.surjective
#align homeomorph.surjective Homeomorph.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ₜ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ₜ β :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert f.symm.continuous }
#align homeomorph.change_inv Homeomorph.changeInv

@[simp]
theorem symm_comp_self (h : α ≃ₜ β) : h.symm ∘ h = id :=
  funext h.symm_apply_apply
#align homeomorph.symm_comp_self Homeomorph.symm_comp_self

@[simp]
theorem self_comp_symm (h : α ≃ₜ β) : h ∘ h.symm = id :=
  funext h.apply_symm_apply
#align homeomorph.self_comp_symm Homeomorph.self_comp_symm

@[simp]
theorem range_coe (h : α ≃ₜ β) : range h = univ :=
  h.surjective.range_eq
#align homeomorph.range_coe Homeomorph.range_coe

theorem image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage
#align homeomorph.image_symm Homeomorph.image_symm

theorem preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm
#align homeomorph.preimage_symm Homeomorph.preimage_symm

@[simp]
theorem image_preimage (h : α ≃ₜ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s
#align homeomorph.image_preimage Homeomorph.image_preimage

@[simp]
theorem preimage_image (h : α ≃ₜ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s
#align homeomorph.preimage_image Homeomorph.preimage_image

protected theorem inducing (h : α ≃ₜ β) : Inducing h :=
  inducing_of_inducing_compose h.continuous h.symm.continuous <| by
    simp only [symm_comp_self, inducing_id]
#align homeomorph.inducing Homeomorph.inducing

theorem induced_eq (h : α ≃ₜ β) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.inducing.1.symm
#align homeomorph.induced_eq Homeomorph.induced_eq

protected theorem quotientMap (h : α ≃ₜ β) : QuotientMap h :=
  QuotientMap.of_quotientMap_compose h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, QuotientMap.id]
#align homeomorph.quotient_map Homeomorph.quotientMap

theorem coinduced_eq (h : α ≃ₜ β) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.quotientMap.2.symm
#align homeomorph.coinduced_eq Homeomorph.coinduced_eq

protected theorem embedding (h : α ≃ₜ β) : Embedding h :=
  ⟨h.inducing, h.injective⟩
#align homeomorph.embedding Homeomorph.embedding

/-- Homeomorphism given an embedding. -/
noncomputable def ofEmbedding (f : α → β) (hf : Embedding f) : α ≃ₜ Set.range f where
  continuous_toFun := hf.continuous.subtype_mk _
  continuous_invFun := hf.continuous_iff.2 <| by simp [continuous_subtype_val]
  toEquiv := Equiv.ofInjective f hf.inj
#align homeomorph.of_embedding Homeomorph.ofEmbedding

protected theorem secondCountableTopology [TopologicalSpace.SecondCountableTopology β]
    (h : α ≃ₜ β) : TopologicalSpace.SecondCountableTopology α :=
  h.inducing.secondCountableTopology
#align homeomorph.second_countable_topology Homeomorph.secondCountableTopology

theorem isCompact_image {s : Set α} (h : α ≃ₜ β) : IsCompact (h '' s) ↔ IsCompact s :=
  h.embedding.isCompact_iff_isCompact_image.symm
#align homeomorph.is_compact_image Homeomorph.isCompact_image

theorem isCompact_preimage {s : Set β} (h : α ≃ₜ β) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm]; exact h.symm.isCompact_image
#align homeomorph.is_compact_preimage Homeomorph.isCompact_preimage

@[simp]
theorem isPreconnected_image {s : Set α} (h : α ≃ₜ β) :
    IsPreconnected (h '' s) ↔ IsPreconnected s :=
  ⟨fun hs ↦ by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs ↦ hs.image _ h.continuous.continuousOn⟩

@[simp]
theorem isPreconnected_preimage {s : Set β} (h : α ≃ₜ β) :
    IsPreconnected (h ⁻¹' s) ↔ IsPreconnected s := by
  rw [← image_symm, isPreconnected_image]

@[simp]
theorem isConnected_image {s : Set α} (h : α ≃ₜ β) :
    IsConnected (h '' s) ↔ IsConnected s :=
  nonempty_image_iff.and h.isPreconnected_image

@[simp]
theorem isConnected_preimage {s : Set β} (h : α ≃ₜ β) :
    IsConnected (h ⁻¹' s) ↔ IsConnected s := by
  rw [← image_symm, isConnected_image]

@[simp]
theorem comap_cocompact (h : α ≃ₜ β) : comap h (cocompact β) = cocompact α :=
  (comap_cocompact_le h.continuous).antisymm <|
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩
#align homeomorph.comap_cocompact Homeomorph.comap_cocompact

@[simp]
theorem map_cocompact (h : α ≃ₜ β) : map h (cocompact α) = cocompact β := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]
#align homeomorph.map_cocompact Homeomorph.map_cocompact

protected theorem compactSpace [CompactSpace α] (h : α ≃ₜ β) : CompactSpace β where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ
#align homeomorph.compact_space Homeomorph.compactSpace

protected theorem t0Space [T0Space α] (h : α ≃ₜ β) : T0Space β :=
  h.symm.embedding.t0Space
#align homeomorph.t0_space Homeomorph.t0Space

protected theorem t1Space [T1Space α] (h : α ≃ₜ β) : T1Space β :=
  h.symm.embedding.t1Space
#align homeomorph.t1_space Homeomorph.t1Space

protected theorem t2Space [T2Space α] (h : α ≃ₜ β) : T2Space β :=
  h.symm.embedding.t2Space
#align homeomorph.t2_space Homeomorph.t2Space

protected theorem t3Space [T3Space α] (h : α ≃ₜ β) : T3Space β :=
  h.symm.embedding.t3Space
#align homeomorph.t3_space Homeomorph.t3Space

protected theorem denseEmbedding (h : α ≃ₜ β) : DenseEmbedding h :=
  { h.embedding with dense := h.surjective.denseRange }
#align homeomorph.dense_embedding Homeomorph.denseEmbedding

@[simp]
theorem isOpen_preimage (h : α ≃ₜ β) {s : Set β} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.quotientMap.isOpen_preimage
#align homeomorph.is_open_preimage Homeomorph.isOpen_preimage

@[simp]
theorem isOpen_image (h : α ≃ₜ β) {s : Set α} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, isOpen_preimage]
#align homeomorph.is_open_image Homeomorph.isOpen_image

protected theorem isOpenMap (h : α ≃ₜ β) : IsOpenMap h := fun _ => h.isOpen_image.2
#align homeomorph.is_open_map Homeomorph.isOpenMap

@[simp]
theorem isClosed_preimage (h : α ≃ₜ β) {s : Set β} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]
#align homeomorph.is_closed_preimage Homeomorph.isClosed_preimage

@[simp]
theorem isClosed_image (h : α ≃ₜ β) {s : Set α} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, isClosed_preimage]
#align homeomorph.is_closed_image Homeomorph.isClosed_image

protected theorem isClosedMap (h : α ≃ₜ β) : IsClosedMap h := fun _ => h.isClosed_image.2
#align homeomorph.is_closed_map Homeomorph.isClosedMap

protected theorem openEmbedding (h : α ≃ₜ β) : OpenEmbedding h :=
  openEmbedding_of_embedding_open h.embedding h.isOpenMap
#align homeomorph.open_embedding Homeomorph.openEmbedding

protected theorem closedEmbedding (h : α ≃ₜ β) : ClosedEmbedding h :=
  closedEmbedding_of_embedding_closed h.embedding h.isClosedMap
#align homeomorph.closed_embedding Homeomorph.closedEmbedding

protected theorem normalSpace [NormalSpace α] (h : α ≃ₜ β) : NormalSpace β :=
  h.symm.closedEmbedding.normalSpace

protected theorem t4Space [T4Space α] (h : α ≃ₜ β) : T4Space β :=
  h.symm.closedEmbedding.t4Space
#align homeomorph.normal_space Homeomorph.t4Space

theorem preimage_closure (h : α ≃ₜ β) (s : Set β) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _
#align homeomorph.preimage_closure Homeomorph.preimage_closure

theorem image_closure (h : α ≃ₜ β) (s : Set α) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]
#align homeomorph.image_closure Homeomorph.image_closure

theorem preimage_interior (h : α ≃ₜ β) (s : Set β) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _
#align homeomorph.preimage_interior Homeomorph.preimage_interior

theorem image_interior (h : α ≃ₜ β) (s : Set α) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]
#align homeomorph.image_interior Homeomorph.image_interior

theorem preimage_frontier (h : α ≃ₜ β) (s : Set β) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _
#align homeomorph.preimage_frontier Homeomorph.preimage_frontier

theorem image_frontier (h : α ≃ₜ β) (s : Set α) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm, preimage_frontier]
#align homeomorph.image_frontier Homeomorph.image_frontier

@[to_additive]
theorem _root_.HasCompactMulSupport.comp_homeomorph {M} [One M] {f : β → M}
    (hf : HasCompactMulSupport f) (φ : α ≃ₜ β) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_closedEmbedding φ.closedEmbedding
#align has_compact_mul_support.comp_homeomorph HasCompactMulSupport.comp_homeomorph
#align has_compact_support.comp_homeomorph HasCompactSupport.comp_homeomorph

@[simp]
theorem map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
  h.embedding.map_nhds_of_mem _ (by simp)
#align homeomorph.map_nhds_eq Homeomorph.map_nhds_eq

theorem symm_map_nhds_eq (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]
#align homeomorph.symm_map_nhds_eq Homeomorph.symm_map_nhds_eq

theorem nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.inducing.nhds_eq_comap x
#align homeomorph.nhds_eq_comap Homeomorph.nhds_eq_comap

@[simp]
theorem comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]
#align homeomorph.comap_nhds_eq Homeomorph.comap_nhds_eq

/-- If the codomain of a homeomorphism is a locally connected space, then the domain is also
a locally connected space. -/
theorem locallyConnectedSpace [i : LocallyConnectedSpace β] (h : α ≃ₜ β) :
    LocallyConnectedSpace α := by
  have : ∀ x, (𝓝 x).HasBasis (fun s ↦ IsOpen s ∧ h x ∈ s ∧ IsConnected s)
      (h.symm '' ·) := fun x ↦ by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs ↦ ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuousOn

/-- If a bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorphOfContinuousOpen (e : α ≃ β) (h₁ : Continuous e) (h₂ : IsOpenMap e) : α ≃ₜ β where
  continuous_toFun := h₁
  continuous_invFun := by
    rw [continuous_def]
    intro s hs
    convert ← h₂ s hs using 1
    apply e.image_eq_preimage
  toEquiv := e
#align homeomorph.homeomorph_of_continuous_open Homeomorph.homeomorphOfContinuousOpen

@[simp]
theorem comp_continuousOn_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.inducing.continuousOn_iff.symm
#align homeomorph.comp_continuous_on_iff Homeomorph.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} : Continuous (h ∘ f) ↔ Continuous f :=
  h.inducing.continuous_iff.symm
#align homeomorph.comp_continuous_iff Homeomorph.comp_continuous_iff

@[simp]
theorem comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} : Continuous (f ∘ h) ↔ Continuous f :=
  h.quotientMap.continuous_iff.symm
#align homeomorph.comp_continuous_iff' Homeomorph.comp_continuous_iff'

theorem comp_continuousAt_iff (h : α ≃ₜ β) (f : γ → α) (x : γ) :
    ContinuousAt (h ∘ f) x ↔ ContinuousAt f x :=
  h.inducing.continuousAt_iff.symm
#align homeomorph.comp_continuous_at_iff Homeomorph.comp_continuousAt_iff

theorem comp_continuousAt_iff' (h : α ≃ₜ β) (f : β → γ) (x : α) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.inducing.continuousAt_iff' (by simp)
#align homeomorph.comp_continuous_at_iff' Homeomorph.comp_continuousAt_iff'

theorem comp_continuousWithinAt_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) (x : γ) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (h ∘ f) s x :=
  h.inducing.continuousWithinAt_iff
#align homeomorph.comp_continuous_within_at_iff Homeomorph.comp_continuousWithinAt_iff

@[simp]
theorem comp_isOpenMap_iff (h : α ≃ₜ β) {f : γ → α} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine' ⟨_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.comp.left_id f, ← h.symm_comp_self, Function.comp.assoc]
  exact h.symm.isOpenMap.comp hf
#align homeomorph.comp_is_open_map_iff Homeomorph.comp_isOpenMap_iff

@[simp]
theorem comp_isOpenMap_iff' (h : α ≃ₜ β) {f : β → γ} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine' ⟨_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp.right_id f, ← h.self_comp_symm, ← Function.comp.assoc]
  exact hf.comp h.symm.isOpenMap
#align homeomorph.comp_is_open_map_iff' Homeomorph.comp_isOpenMap_iff'

/-- If two sets are equal, then they are homeomorphic. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ₜ t where
  continuous_toFun := continuous_inclusion h.subset
  continuous_invFun := continuous_inclusion h.symm.subset
  toEquiv := Equiv.setCongr h
#align homeomorph.set_congr Homeomorph.setCongr

/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : Sum α γ ≃ₜ Sum β δ where
  continuous_toFun := h₁.continuous.sum_map h₂.continuous
  continuous_invFun := h₁.symm.continuous.sum_map h₂.symm.continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv
#align homeomorph.sum_congr Homeomorph.sumCongr

/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ where
  continuous_toFun := h₁.continuous.prod_map h₂.continuous
  continuous_invFun := h₁.symm.continuous.prod_map h₂.symm.continuous
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align homeomorph.prod_congr Homeomorph.prodCongr

@[simp]
theorem prodCongr_symm (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align homeomorph.prod_congr_symm Homeomorph.prodCongr_symm

@[simp]
theorem coe_prodCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align homeomorph.coe_prod_congr Homeomorph.coe_prodCongr

section

variable (α β γ)

/-- `α × β` is homeomorphic to `β × α`. -/
def prodComm : α × β ≃ₜ β × α where
  continuous_toFun := continuous_snd.prod_mk continuous_fst
  continuous_invFun := continuous_snd.prod_mk continuous_fst
  toEquiv := Equiv.prodComm α β
#align homeomorph.prod_comm Homeomorph.prodComm

@[simp]
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl
#align homeomorph.prod_comm_symm Homeomorph.prodComm_symm

@[simp]
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl
#align homeomorph.coe_prod_comm Homeomorph.coe_prodComm

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ₜ α × β × γ where
  continuous_toFun := continuous_fst.fst.prod_mk (continuous_fst.snd.prod_mk continuous_snd)
  continuous_invFun := (continuous_fst.prod_mk continuous_snd.fst).prod_mk continuous_snd.snd
  toEquiv := Equiv.prodAssoc α β γ
#align homeomorph.prod_assoc Homeomorph.prodAssoc

/-- `α × {*}` is homeomorphic to `α`. -/
@[simps! (config := { fullyApplied := false }) apply]
def prodPUnit : α × PUnit ≃ₜ α where
  toEquiv := Equiv.prodPUnit α
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prod_mk continuous_const
#align homeomorph.prod_punit Homeomorph.prodPUnit

/-- `{*} × α` is homeomorphic to `α`. -/
def punitProd : PUnit × α ≃ₜ α :=
  (prodComm _ _).trans (prodPUnit _)
#align homeomorph.punit_prod Homeomorph.punitProd

@[simp] theorem coe_punitProd : ⇑(punitProd α) = Prod.snd := rfl
#align homeomorph.coe_punit_prod Homeomorph.coe_punitProd

/-- If both `α` and `β` have a unique element, then `α ≃ₜ β`. -/
@[simps!]
def homeomorphOfUnique [Unique α] [Unique β] : α ≃ₜ β :=
  { Equiv.equivOfUnique α β with
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }
#align homeomorph.homeomorph_of_unique Homeomorph.homeomorphOfUnique

end

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, β (e i) ≃ₜ Π j, β j` obtained from a bijection `ι ≃ ι'`. -/
@[simps! apply toEquiv]
def piCongrLeft {ι ι' : Type*} {β : ι' → Type*} [∀ j, TopologicalSpace (β j)]
    (e : ι ≃ ι') : (∀ i, β (e i)) ≃ₜ ∀ j, β j where
  continuous_toFun := continuous_pi <| e.forall_congr_left.mp <| fun i ↦ by
    simpa only [Equiv.toFun_as_coe_apply, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, β₁ i ≃ₜ Π j, β₂ i` obtained from homeomorphisms `β₁ i ≃ₜ β₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, TopologicalSpace (β₁ i)]
    [∀ i, TopologicalSpace (β₂ i)] (F : ∀ i, β₁ i ≃ₜ β₂ i) : (∀ i, β₁ i) ≃ₜ ∀ i, β₂ i where
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (F i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (F i).symm.continuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv
#align homeomorph.Pi_congr_right Homeomorph.piCongrRight

@[simp]
theorem piCongrRight_symm {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, TopologicalSpace (β₁ i)]
    [∀ i, TopologicalSpace (β₂ i)] (F : ∀ i, β₁ i ≃ₜ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl
#align homeomorph.Pi_congr_right_symm Homeomorph.piCongrRight_symm

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, β₁ i ≃ₜ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`β₁ i₁ ≃ₜ β₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (β₁ i₁)] [∀ i₂, TopologicalSpace (β₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, β₁ i₁ ≃ₜ β₂ (e i₁)) : (∀ i₁, β₁ i₁) ≃ₜ ∀ i₂, β₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

-- porting note: TODO: align the order of universes with `Equiv.ulift`
/-- `ULift α` is homeomorphic to `α`. -/
def ulift.{u, v} {α : Type u} [TopologicalSpace α] : ULift.{v, u} α ≃ₜ α where
  continuous_toFun := continuous_uLift_down
  continuous_invFun := continuous_uLift_up
  toEquiv := Equiv.ulift
#align homeomorph.ulift Homeomorph.ulift

section Distrib

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sumProdDistrib : Sum α β × γ ≃ₜ Sum (α × γ) (β × γ) :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sumProdDistrib α β γ).symm
        ((continuous_inl.prod_map continuous_id).sum_elim
          (continuous_inr.prod_map continuous_id)) <|
      (isOpenMap_inl.prod IsOpenMap.id).sum_elim (isOpenMap_inr.prod IsOpenMap.id)
#align homeomorph.sum_prod_distrib Homeomorph.sumProdDistrib

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prodSumDistrib : α × Sum β γ ≃ₜ Sum (α × β) (α × γ) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)
#align homeomorph.prod_sum_distrib Homeomorph.prodSumDistrib

variable {ι : Type*} {σ : ι → Type*} [∀ i, TopologicalSpace (σ i)]

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigmaProdDistrib : (Σi, σ i) × β ≃ₜ Σi, σ i × β :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sigmaProdDistrib σ β).symm
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prod_mk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prod IsOpenMap.id)
#align homeomorph.sigma_prod_distrib Homeomorph.sigmaProdDistrib

end Distrib

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps! (config := { fullyApplied := false })]
def funUnique (ι α : Type*) [Unique ι] [TopologicalSpace α] : (ι → α) ≃ₜ α where
  toEquiv := Equiv.funUnique ι α
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id
#align homeomorph.fun_unique Homeomorph.funUnique

/-- Homeomorphism between dependent functions `Π i : Fin 2, α i` and `α 0 × α 1`. -/
@[simps! (config := { fullyApplied := false })]
def piFinTwo.{u} (α : Fin 2 → Type u) [∀ i, TopologicalSpace (α i)] : (∀ i, α i) ≃ₜ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  continuous_toFun := (continuous_apply 0).prod_mk (continuous_apply 1)
  continuous_invFun := continuous_pi <| Fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩
#align homeomorph.pi_fin_two Homeomorph.piFinTwo

/-- Homeomorphism between `α² = Fin 2 → α` and `α × α`. -/
@[simps! (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ₜ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }
#align homeomorph.fin_two_arrow Homeomorph.finTwoArrow

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
def image (e : α ≃ₜ β) (s : Set α) : s ≃ₜ e '' s where
  -- porting note: todo: by continuity!
  continuous_toFun := e.continuous.continuousOn.restrict_mapsTo (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s
#align homeomorph.image Homeomorph.image

/-- `Set.univ α` is homeomorphic to `α`. -/
@[simps! (config := { fullyApplied := false })]
def Set.univ (α : Type*) [TopologicalSpace α] : (univ : Set α) ≃ₜ α where
  toEquiv := Equiv.Set.univ α
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _
#align homeomorph.set.univ Homeomorph.Set.univ

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prod_mk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prod_mk continuous_subtype_val.snd').subtype_mk _
#align homeomorph.set.prod Homeomorph.Set.prod

section

variable {ι : Type*}

/-- The topological space `Π i, β i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not.-/
@[simps!]
def piEquivPiSubtypeProd (p : ι → Prop) (β : ι → Type*) [∀ i, TopologicalSpace (β i)]
    [DecidablePred p] : (∀ i, β i) ≃ₜ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i
    where
  toEquiv := Equiv.piEquivPiSubtypeProd p β
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
def piSplitAt (β : ι → Type*) [∀ j, TopologicalSpace (β j)] :
    (∀ j, β j) ≃ₜ β i × ∀ j : { j // j ≠ i }, β j
    where
  toEquiv := Equiv.piSplitAt i β
  continuous_toFun := (continuous_apply i).prod_mk (continuous_pi fun j => continuous_apply j.1)
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      subst h
      exacts [continuous_fst, (continuous_apply _).comp continuous_snd]
#align homeomorph.pi_split_at Homeomorph.piSplitAt

variable (β)

/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps!]
def funSplitAt : (ι → β) ≃ₜ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _
#align homeomorph.fun_split_at Homeomorph.funSplitAt

end

end Homeomorph

namespace Equiv
variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- An equiv between topological spaces respecting openness is a homeomorphism. -/
@[simps toEquiv]
def toHomeomorph (e : α ≃ β) (he : ∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : α ≃ₜ β where
  toEquiv := e
  continuous_toFun := continuous_def.2 λ s ↦ (he _).2
  continuous_invFun := continuous_def.2 λ s ↦ by convert (he _).1; simp

@[simp] lemma coe_toHomeomorph (e : α ≃ β) (he) : ⇑(e.toHomeomorph he) = e := rfl
lemma toHomeomorph_apply (e : α ≃ β) (he) (a : α) : e.toHomeomorph he a = e a := rfl

@[simp] lemma toHomeomorph_refl :
  (Equiv.refl α).toHomeomorph (λ _s ↦ Iff.rfl) = Homeomorph.refl _ := rfl

@[simp] lemma toHomeomorph_symm (e : α ≃ β) (he) :
  (e.toHomeomorph he).symm = e.symm.toHomeomorph λ s ↦ by convert (he _).symm; simp := rfl

lemma toHomeomorph_trans (e : α ≃ β) (f : β ≃ γ) (he hf) :
    (e.trans f).toHomeomorph (λ _s ↦ (he _).trans (hf _)) =
    (e.toHomeomorph he).trans (f.toHomeomorph hf) := rfl

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps toEquiv] -- porting note: TODO: was `@[simps]`
def toHomeomorphOfInducing (f : α ≃ β) (hf : Inducing f) : α ≃ₜ β :=
  { f with
    continuous_toFun := hf.continuous
    continuous_invFun := hf.continuous_iff.2 <| by simpa using continuous_id }
#align equiv.to_homeomorph_of_inducing Equiv.toHomeomorphOfInducing

end Equiv

namespace Continuous

variable [TopologicalSpace α] [TopologicalSpace β]

theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace α] [T2Space β] {f : α ≃ β}
    (hf : Continuous f) : Continuous f.symm := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage] at hC'
#align continuous.continuous_symm_of_equiv_compact_to_t2 Continuous.continuous_symm_of_equiv_compact_to_t2

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv] -- porting note: was `@[simps]`
def homeoOfEquivCompactToT2 [CompactSpace α] [T2Space β] {f : α ≃ β} (hf : Continuous f) : α ≃ₜ β :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }
#align continuous.homeo_of_equiv_compact_to_t2 Continuous.homeoOfEquivCompactToT2

end Continuous
