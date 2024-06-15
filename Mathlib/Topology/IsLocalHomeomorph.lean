/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.SeparatedMap

#align_import topology.is_locally_homeomorph from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

For a function `f : X → Y ` between topological spaces, we say
* `IsLocalHomeomorphOn f s` if `f` is a local homeomorphism around each point of `s`: for each
  `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.
* `IsLocalHomeomorph f`: `f` is a local homeomorphism, i.e. it's a local homeomorphism on `univ`.

Note that `IsLocalHomeomorph` is a global condition. This is in contrast to
`PartialHomeomorph`, which is a homeomorphism between specific open subsets.

## Main results
* local homeomorphisms are locally injective open maps
* more!

-/


open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

/-- A function `f : X → Y` satisfies `IsLocalHomeomorphOn f s` if each `x ∈ s` is contained in
the source of some `e : PartialHomeomorph X Y` with `f = e`. -/
def IsLocalHomeomorphOn :=
  ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph_on IsLocalHomeomorphOn

theorem isLocalHomeomorphOn_iff_openEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorphOn f s ↔ ∀ x ∈ s, ∃ U ∈ 𝓝 x, OpenEmbedding (U.restrict f) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.openEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : OpenEmbedding ((interior U).restrict f) := by
      refine emb.comp ⟨embedding_inclusion interior_subset, ?_⟩
      rw [Set.range_inclusion]; exact isOpen_induced isOpen_interior
    obtain ⟨cont, inj, openMap⟩ := openEmbedding_iff_continuous_injective_open.mp this
    haveI : Nonempty X := ⟨x⟩
    exact ⟨PartialHomeomorph.ofContinuousOpenRestrict
      (Set.injOn_iff_injective.mpr inj).toPartialEquiv
      (continuousOn_iff_continuous_restrict.mpr cont) openMap isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hU, rfl⟩

namespace IsLocalHomeomorphOn

/-- Proves that `f` satisfies `IsLocalHomeomorphOn f s`. The condition `h` is weaker than the
definition of `IsLocalHomeomorphOn f s`, since it only requires `e : PartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx ↦ by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx ↦ by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy ↦ by rw [he (e.map_target' hy)]; exact e.right_inv' hy
        continuousOn_toFun := (continuousOn_congr he).mpr e.continuousOn_toFun },
      hx, rfl⟩
#align is_locally_homeomorph_on.mk IsLocalHomeomorphOn.mk

/-- A `PartialHomeomorph` is a local homeomorphism on its source. -/
lemma PartialHomeomorph.isLocalHomeomorphOn (e : PartialHomeomorph X Y) :
    IsLocalHomeomorphOn e e.source :=
  fun _ hx ↦ ⟨e, hx, rfl⟩

variable {g f s t}

theorem mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s ⊆ t) : IsLocalHomeomorphOn f s :=
  fun x hx ↦ hf x (hst hx)

theorem of_comp_left (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
    (cont : ∀ x ∈ s, ContinuousAt f x) : IsLocalHomeomorphOn f s := mk f s fun x hx ↦ by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy ↦ ?_⟩
  change f y = g.symm (gf y)
  have : f y ∈ g.source := by apply interior_subset hy.1.2
  rw [← he, g.eq_symm_apply this (by apply g.map_source this), Function.comp_apply]

theorem of_comp_right (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s) :
    IsLocalHomeomorphOn g (f '' s) := mk g _ <| by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy ↦ ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he, Function.comp_apply, f.right_inv hy.1]

theorem map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx
#align is_locally_homeomorph_on.map_nhds_eq IsLocalHomeomorphOn.map_nhds_eq

protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le
#align is_locally_homeomorph_on.continuous_at IsLocalHomeomorphOn.continuousAt

protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  ContinuousAt.continuousOn fun _x ↦ hf.continuousAt
#align is_locally_homeomorph_on.continuous_on IsLocalHomeomorphOn.continuousOn

protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
#align is_locally_homeomorph_on.comp IsLocalHomeomorphOn.comp

end IsLocalHomeomorphOn

/-- A function `f : X → Y` satisfies `IsLocalHomeomorph f` if each `x : x` is contained in
  the source of some `e : PartialHomeomorph X Y` with `f = e`. -/
def IsLocalHomeomorph :=
  ∀ x : X, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph IsLocalHomeomorph

theorem Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f :=
  fun _ ↦ ⟨f.toPartialHomeomorph, trivial, rfl⟩

variable {f s}

theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ :=
  ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩
#align is_locally_homeomorph_iff_is_locally_homeomorph_on_univ isLocalHomeomorph_iff_isLocalHomeomorphOn_univ

protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f s := fun x _ ↦ hf x
#align is_locally_homeomorph.is_locally_homeomorph_on IsLocalHomeomorph.isLocalHomeomorphOn

theorem isLocalHomeomorph_iff_openEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorph f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, OpenEmbedding (U.restrict f) := by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_openEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

theorem OpenEmbedding.isLocalHomeomorph (hf : OpenEmbedding f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_openEmbedding_restrict.mpr fun _ ↦
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).openEmbedding⟩

variable (f)

namespace IsLocalHomeomorph

/-- Proves that `f` satisfies `IsLocalHomeomorph f`. The condition `h` is weaker than the
definition of `IsLocalHomeomorph f`, since it only requires `e : PartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx ↦ h x)
#align is_locally_homeomorph.mk IsLocalHomeomorph.mk

/-- A homeomorphism is a local homeomorphism. -/
lemma Homeomorph.isLocalHomeomorph (h : X ≃ₜ Y) : IsLocalHomeomorph h :=
  fun _ ↦ ⟨h.toPartialHomeomorph, trivial, rfl⟩

variable {g f}

lemma isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f :=
  fun x ↦ by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

theorem of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
    (cont : Continuous f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ ↦ cont.continuousAt

theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)
#align is_locally_homeomorph.map_nhds_eq IsLocalHomeomorph.map_nhds_eq

/-- A local homeomorphism is continuous. -/
protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isLocalHomeomorphOn.continuousOn
#align is_locally_homeomorph.continuous IsLocalHomeomorph.continuous

/-- A local homeomorphism is an open map. -/
protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x ↦ ge_of_eq (hf.map_nhds_eq x)
#align is_locally_homeomorph.is_open_map IsLocalHomeomorph.isOpenMap

/-- The composition of local homeomorphisms is a local homeomorphism. -/
protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))
#align is_locally_homeomorph.comp IsLocalHomeomorph.comp

/-- An injective local homeomorphism is an open embedding. -/
theorem openEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective) :
    OpenEmbedding f :=
  openEmbedding_of_continuous_injective_open hf.continuous hi hf.isOpenMap

/-- A surjective embedding is a homeomorphism. -/
noncomputable def _root_.Embedding.toHomeomeomorph_of_surjective (hf : Embedding f)
    (hsurj : Function.Surjective f) : X ≃ₜ Y :=
  Homeomorph.homeomorphOfContinuousOpen (Equiv.ofBijective f ⟨hf.inj, hsurj⟩)
    hf.continuous (hf.toOpenEmbedding_of_surjective hsurj).isOpenMap

/-- A bijective local homeomorphism is a homeomorphism. -/
noncomputable def toHomeomorph_of_bijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) :
    X ≃ₜ Y :=
  Homeomorph.homeomorphOfContinuousOpen (Equiv.ofBijective f hb) hf.continuous hf.isOpenMap

/-- Continuous local sections of a local homeomorphism are open embeddings. -/
theorem openEmbedding_of_comp (hf : IsLocalHomeomorph g) (hgf : OpenEmbedding (g ∘ f))
    (cont : Continuous f) : OpenEmbedding f :=
  (hgf.isLocalHomeomorph.of_comp hf cont).openEmbedding_of_injective hgf.inj.of_comp

open TopologicalSpace in
/-- Ranges of continuous local sections of a local homeomorphism
form a basis of the source space. -/
theorem isTopologicalBasis (hf : IsLocalHomeomorph f) : IsTopologicalBasis
    {U : Set X | ∃ V : Set Y, IsOpen V ∧ ∃ s : C(V,X), f ∘ s = (↑) ∧ Set.range s = U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU ↦ ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (openEmbedding_of_comp hf (hs ▸ ⟨embedding_subtype_val, ?_⟩) s.continuous).isOpen_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source ∩ U, ⟨f.target ∩ f.symm ⁻¹' U, f.symm.isOpen_inter_preimage hU,
      ⟨_, continuousOn_iff_continuous_restrict.mp (f.continuousOn_invFun.mono fun _ h ↦ h.1)⟩,
      ?_, (Set.range_restrict _ _).trans ?_⟩, ⟨hxf, hx⟩, fun _ h ↦ h.2⟩
    · ext y; exact f.right_inv y.2.1
    · apply (f.symm_image_target_inter_eq _).trans
      rw [Set.preimage_inter, ← Set.inter_assoc, Set.inter_eq_self_of_subset_left
        f.source_preimage_target, f.source_inter_preimage_inv_preimage]

end IsLocalHomeomorph
