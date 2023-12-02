/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.SeparatedMap

#align_import topology.is_locally_homeomorph from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

* `IsLocallyHomeomorph`: A function `f : X → Y` satisfies `IsLocallyHomeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `IsLocallyHomeomorph` is a global condition. This is in contrast to
  `LocalHomeomorph`, which is a homeomorphism between specific open subsets.
-/


open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

/-- A function `f : X → Y` satisfies `IsLocallyHomeomorphOn f s` if each `x ∈ s` is contained in
the source of some `e : LocalHomeomorph X Y` with `f = e`. -/
def IsLocallyHomeomorphOn :=
  ∀ x ∈ s, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph_on IsLocallyHomeomorphOn

theorem isLocallyHomeomorphOn_iff_openEmbedding_restrict {f : X → Y} :
    IsLocallyHomeomorphOn f s ↔ ∀ x ∈ s, ∃ U ∈ 𝓝 x, OpenEmbedding (U.restrict f) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.openEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : OpenEmbedding ((interior U).restrict f)
    · refine emb.comp ⟨embedding_inclusion interior_subset, ?_⟩
      rw [Set.range_inclusion]; exact isOpen_induced isOpen_interior
    obtain ⟨cont, inj, openMap⟩ := openEmbedding_iff_continuous_injective_open.mp this
    haveI : Nonempty X := ⟨x⟩
    exact ⟨LocalHomeomorph.ofContinuousOpenRestrict (Set.injOn_iff_injective.mpr inj).toLocalEquiv
      (continuousOn_iff_continuous_restrict.mpr cont) openMap isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hU, rfl⟩

namespace IsLocallyHomeomorphOn

/-- Proves that `f` satisfies `IsLocallyHomeomorphOn f s`. The condition `h` is weaker than the
definition of `IsLocallyHomeomorphOn f s`, since it only requires `e : LocalHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x ∈ s, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocallyHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun x hx => by rw [he x hx]; exact e.map_source' hx
        left_inv' := fun x hx => by rw [he x hx]; exact e.left_inv' hx
        right_inv' := fun y hy => by rw [he _ (e.map_target' hy)]; exact e.right_inv' hy
        continuous_toFun := (continuousOn_congr he).mpr e.continuous_toFun },
      hx, rfl⟩
#align is_locally_homeomorph_on.mk IsLocallyHomeomorphOn.mk

variable {g f s t}

theorem mono {t : Set X} (hf : IsLocallyHomeomorphOn f t) (hst : s ⊆ t) :
    IsLocallyHomeomorphOn f s := fun x hx ↦ hf x (hst hx)

theorem of_comp_left (hgf : IsLocallyHomeomorphOn (g ∘ f) s) (hg : IsLocallyHomeomorphOn g (f '' s))
    (cont : ∀ x ∈ s, ContinuousAt f x) : IsLocallyHomeomorphOn f s := mk f s fun x hx ↦ by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy ↦ ?_⟩
  change f y = g.symm (gf y)
  have : f y ∈ g.source := by apply interior_subset hy.1.2
  rw [← he, g.eq_symm_apply this (by apply g.map_source this)]
  rfl

theorem of_comp_right (hgf : IsLocallyHomeomorphOn (g ∘ f) s) (hf : IsLocallyHomeomorphOn f s) :
    IsLocallyHomeomorphOn g (f '' s) := mk g _ <| by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy ↦ ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he, Function.comp_apply, f.right_inv hy.1]

theorem map_nhds_eq (hf : IsLocallyHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx
#align is_locally_homeomorph_on.map_nhds_eq IsLocallyHomeomorphOn.map_nhds_eq

protected theorem continuousAt (hf : IsLocallyHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le
#align is_locally_homeomorph_on.continuous_at IsLocallyHomeomorphOn.continuousAt

protected theorem continuousOn (hf : IsLocallyHomeomorphOn f s) : ContinuousOn f s :=
  ContinuousAt.continuousOn fun _x => hf.continuousAt
#align is_locally_homeomorph_on.continuous_on IsLocallyHomeomorphOn.continuousOn

protected theorem comp (hg : IsLocallyHomeomorphOn g t) (hf : IsLocallyHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocallyHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
#align is_locally_homeomorph_on.comp IsLocallyHomeomorphOn.comp

end IsLocallyHomeomorphOn

/-- A function `f : X → Y` satisfies `IsLocallyHomeomorph f` if each `x : x` is contained in
  the source of some `e : LocalHomeomorph X Y` with `f = e`. -/
def IsLocallyHomeomorph :=
  ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph IsLocallyHomeomorph

theorem Homeomorph.isLocallyHomeomorph (f : X ≃ₜ Y) : IsLocallyHomeomorph f :=
  fun _ ↦ ⟨f.toLocalHomeomorph, trivial, rfl⟩

variable {f s}

theorem isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ :
    IsLocallyHomeomorph f ↔ IsLocallyHomeomorphOn f Set.univ :=
  ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩
#align is_locally_homeomorph_iff_is_locally_homeomorph_on_univ isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ

protected theorem IsLocallyHomeomorph.isLocallyHomeomorphOn (hf : IsLocallyHomeomorph f) :
    IsLocallyHomeomorphOn f s := fun x _ ↦ hf x
#align is_locally_homeomorph.is_locally_homeomorph_on IsLocallyHomeomorph.isLocallyHomeomorphOn

theorem isLocallyHomeomorph_iff_openEmbedding_restrict {f : X → Y} :
    IsLocallyHomeomorph f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, OpenEmbedding (U.restrict f) := by
  simp_rw [isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ,
    isLocallyHomeomorphOn_iff_openEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

theorem OpenEmbedding.isLocallyHomeomorph (hf : OpenEmbedding f) : IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_openEmbedding_restrict.mpr fun _ ↦
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).openEmbedding⟩

variable (f)

namespace IsLocallyHomeomorph

/-- Proves that `f` satisfies `IsLocallyHomeomorph f`. The condition `h` is weaker than the
definition of `IsLocallyHomeomorph f`, since it only requires `e : LocalHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr
    (IsLocallyHomeomorphOn.mk f Set.univ fun x _hx => h x)
#align is_locally_homeomorph.mk IsLocallyHomeomorph.mk

variable {g f}

lemma isLocallyInjective (hf : IsLocallyHomeomorph f) : IsLocallyInjective f :=
  fun x ↦ by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

theorem of_comp (hgf : IsLocallyHomeomorph (g ∘ f)) (hg : IsLocallyHomeomorph g)
    (cont : Continuous f) : IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr <|
    hgf.isLocallyHomeomorphOn.of_comp_left hg.isLocallyHomeomorphOn fun _ _ ↦ cont.continuousAt

theorem map_nhds_eq (hf : IsLocallyHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocallyHomeomorphOn.map_nhds_eq (Set.mem_univ x)
#align is_locally_homeomorph.map_nhds_eq IsLocallyHomeomorph.map_nhds_eq

protected theorem continuous (hf : IsLocallyHomeomorph f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isLocallyHomeomorphOn.continuousOn
#align is_locally_homeomorph.continuous IsLocallyHomeomorph.continuous

protected theorem isOpenMap (hf : IsLocallyHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)
#align is_locally_homeomorph.is_open_map IsLocallyHomeomorph.isOpenMap

protected theorem comp (hg : IsLocallyHomeomorph g) (hf : IsLocallyHomeomorph f) :
    IsLocallyHomeomorph (g ∘ f) :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr
    (hg.isLocallyHomeomorphOn.comp hf.isLocallyHomeomorphOn (Set.univ.mapsTo_univ f))
#align is_locally_homeomorph.comp IsLocallyHomeomorph.comp

theorem openEmbedding_of_injective (hf : IsLocallyHomeomorph f) (hi : f.Injective) :
    OpenEmbedding f :=
  openEmbedding_of_continuous_injective_open hf.continuous hi hf.isOpenMap

/-- Continuous local sections of a local homeomorphism are open embeddings. -/
theorem openEmbedding_of_comp (hf : IsLocallyHomeomorph g) (hgf : OpenEmbedding (g ∘ f))
    (cont : Continuous f) : OpenEmbedding f :=
  (hgf.isLocallyHomeomorph.of_comp hf cont).openEmbedding_of_injective hgf.inj.of_comp

open TopologicalSpace in
/-- Ranges of continuous local sections of a local homeomorphism form a basis of the source space.-/
theorem isTopologicalBasis (hf : IsLocallyHomeomorph f) : IsTopologicalBasis
    {U : Set X | ∃ V : Set Y, IsOpen V ∧ ∃ s : C(V,X), f ∘ s = (↑) ∧ Set.range s = U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU ↦ ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (openEmbedding_of_comp hf (hs ▸ ⟨embedding_subtype_val, ?_⟩) s.continuous).open_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source ∩ U, ⟨f.target ∩ f.symm ⁻¹' U, f.symm.isOpen_inter_preimage hU,
      ⟨_, continuousOn_iff_continuous_restrict.mp (f.continuous_invFun.mono fun _ h ↦ h.1)⟩,
      ?_, (Set.range_restrict _ _).trans ?_⟩, ⟨hxf, hx⟩, fun _ h ↦ h.2⟩
    · ext y; exact f.right_inv y.2.1
    · apply (f.symm_image_target_inter_eq _).trans
      rw [Set.preimage_inter, ← Set.inter_assoc, Set.inter_eq_self_of_subset_left
        f.source_preimage_target, f.source_inter_preimage_inv_preimage]

end IsLocallyHomeomorph
