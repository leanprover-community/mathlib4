/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph
public import Mathlib.Topology.SeparatedMap

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
`OpenPartialHomeomorph`, which is a homeomorphism between specific open subsets.

## Main results
* local homeomorphisms are locally injective open maps
* more!

-/

@[expose] public section


open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

/-- A function `f : X → Y` satisfies `IsLocalHomeomorphOn f s` if each `x ∈ s` is contained in
the source of some `e : OpenPartialHomeomorph X Y` with `f = e`. -/
def IsLocalHomeomorphOn :=
  ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e

/-- A `OpenPartialHomeomorph` is a local homeomorphism on its source. -/
lemma OpenPartialHomeomorph.isLocalHomeomorphOn (e : OpenPartialHomeomorph X Y) :
    IsLocalHomeomorphOn e e.source :=
  fun _ hx ↦ ⟨e, hx, rfl⟩

variable {s} in
theorem isLocalHomeomorphOn_iff_isOpenEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorphOn f s ↔ ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.restrict f) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.isOpenEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : IsOpenEmbedding ((interior U).restrict f) := by
      refine emb.comp ⟨.inclusion interior_subset, ?_⟩
      rw [Set.range_inclusion]; exact isOpen_induced isOpen_interior
    obtain ⟨cont, inj, openMap⟩ := isOpenEmbedding_iff_continuous_injective_isOpenMap.mp this
    haveI : Nonempty X := ⟨x⟩
    exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict
      (Set.injOn_iff_injective.mpr inj).toPartialEquiv
      (continuousOn_iff_continuous_restrict.mpr cont) openMap isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hU, rfl⟩

namespace IsLocalHomeomorphOn

variable {f s}

theorem discreteTopology_of_image (h : IsLocalHomeomorphOn f s)
    [DiscreteTopology (f '' s)] : DiscreteTopology s :=
  discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    obtain ⟨e, hx, rfl⟩ := h x x.2
    have ⟨U, hU, eq⟩ := isOpen_discrete {(⟨_, _, x.2, rfl⟩ : e '' s)}
    refine ⟨e.source ∩ e ⁻¹' U, e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU,
      subset_antisymm (fun x' mem ↦ Subtype.ext <| e.injOn mem.1 hx ?_) ?_⟩
    · exact Subtype.ext_iff.mp (eq.subset (a := ⟨_, x', x'.2, rfl⟩) mem.2)
    · rintro x rfl; exact ⟨hx, eq.superset rfl⟩

lemma isDiscrete_of_image (h : IsLocalHomeomorphOn f s)
    (hs : IsDiscrete (f '' s)) : IsDiscrete s :=
  have := hs.1; ⟨discreteTopology_of_image h⟩

theorem discreteTopology_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    DiscreteTopology (f '' s) ↔ DiscreteTopology s := by
  refine ⟨fun _ ↦ h.discreteTopology_of_image, ?_⟩
  simp_rw [discreteTopology_iff_isOpen_singleton]
  rintro hX ⟨_, x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := h x hx
  refine ⟨e '' {x}, e.isOpen_image_of_subset_source ?_ (Set.singleton_subset_iff.mpr hxe), ?_⟩
  · simpa using hs.isOpenMap_subtype_val _ (hX ⟨x, hx⟩)
  · ext; simp [Subtype.ext_iff]

lemma isDiscrete_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    IsDiscrete (f '' s) ↔ IsDiscrete s :=
  ⟨h.isDiscrete_of_image, fun hs' ↦ ⟨h.discreteTopology_image_iff hs |>.mpr hs'.to_subtype⟩⟩

variable (f s) in
/-- Proves that `f` satisfies `IsLocalHomeomorphOn f s`. The condition `h` is weaker than the
definition of `IsLocalHomeomorphOn f s`, since it only requires `e : OpenPartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
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

@[deprecated (since := "2025-11-05")]
alias OpenPartialHomeomorph.isLocalHomeomorphOn := _root_.OpenPartialHomeomorph.isLocalHomeomorphOn

variable {g t}

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

protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le

protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  continuousOn_of_forall_continuousAt fun _x ↦ hf.continuousAt

protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

end IsLocalHomeomorphOn

/-- A function `f : X → Y` satisfies `IsLocalHomeomorph f` if each `x : x` is contained in
  the source of some `e : OpenPartialHomeomorph X Y` with `f = e`. -/
def IsLocalHomeomorph :=
  ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e

/-- A homeomorphism is a local homeomorphism. -/
theorem Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f :=
  fun _ ↦ ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

variable {f s}

theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ :=
  ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩

protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f s := fun x _ ↦ hf x

theorem isLocalHomeomorph_iff_isOpenEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorph f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.restrict f) := by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

theorem Topology.IsOpenEmbedding.isLocalHomeomorph (hf : IsOpenEmbedding f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ ↦
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

namespace IsLocalHomeomorph

/-- A space that admits a local homeomorphism to a discrete space is itself discrete. -/
theorem comap_discreteTopology (h : IsLocalHomeomorph f)
    [DiscreteTopology Y] : DiscreteTopology X :=
  (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image

theorem discreteTopology_range_iff (h : IsLocalHomeomorph f) :
    DiscreteTopology (Set.range f) ↔ DiscreteTopology X := by
  rw [← Set.image_univ, ← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

/-- If there is a surjective local homeomorphism between two spaces and one of them is discrete,
then both spaces are discrete. -/
theorem discreteTopology_iff_of_surjective (h : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    DiscreteTopology X ↔ DiscreteTopology Y := by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff, ← hs.range_eq, h.discreteTopology_range_iff]

variable (f)

/-- Proves that `f` satisfies `IsLocalHomeomorph f`. The condition `h` is weaker than the
definition of `IsLocalHomeomorph f`, since it only requires `e : OpenPartialHomeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx ↦ h x)

@[deprecated (since := "2025-11-05")]
alias Homeomorph.isLocalHomeomorph := _root_.Homeomorph.isLocalHomeomorph

variable {g f}

lemma isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f :=
  fun x ↦ by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

theorem of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
    (cont : Continuous f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ ↦ cont.continuousAt

theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

/-- A local homeomorphism is continuous. -/
protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn

/-- A local homeomorphism is an open map. -/
protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x ↦ ge_of_eq (hf.map_nhds_eq x)

/-- The composition of local homeomorphisms is a local homeomorphism. -/
protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))

/-- An injective local homeomorphism is an open embedding. -/
theorem isOpenEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective) :
    IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

/-- A bijective local homeomorphism is a homeomorphism. -/
noncomputable def toHomeomorph_of_bijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) :
    X ≃ₜ Y :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap

/-- Continuous local sections of a local homeomorphism are open embeddings. -/
theorem isOpenEmbedding_of_comp (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f))
    (cont : Continuous f) : IsOpenEmbedding f :=
  (hgf.isLocalHomeomorph.of_comp hf cont).isOpenEmbedding_of_injective hgf.injective.of_comp

variable {t} in
theorem isOpenEmbedding_section (hf : IsLocalHomeomorph f) (ht : IsOpen t) {sec : t → X}
    (hsec : f ∘ sec = (↑)) (cont : Continuous sec) : IsOpenEmbedding sec :=
  hf.isOpenEmbedding_of_comp (hsec ▸ ht.isOpenEmbedding_subtypeVal) cont

variable (s) in
theorem isOpen_injOn_tfae (hf : IsLocalHomeomorph f) : List.TFAE
    [IsOpen s ∧ s.InjOn f,
      IsOpenEmbedding (s.restrict f),
      IsOpen (f '' s) ∧ ∃ h : s.InjOn f, Continuous (Equiv.ofInjective _ h.injective).symm,
      IsOpen (f '' s) ∧ ∃ sec : C(f '' s, X), f ∘ sec = (↑) ∧ Set.range sec = s,
      ∃ U : Set Y, IsOpen U ∧ ∃ sec : C(U, X), f ∘ sec = (↑) ∧ Set.range sec = s] := by
  tfae_have 1 → 2 := fun h ↦ isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨hf.continuous
    |>.comp continuous_subtype_val, h.2.injective, hf.isOpenMap.comp h.1.isOpenMap_subtype_val⟩
  tfae_have 2 → 3 := fun h ↦ ⟨Set.range_restrict .. ▸ h.isOpen_range,
    Set.injOn_iff_injective.mpr h.injective, h.toHomeomorph.symm.continuous⟩
  tfae_have 3 → 4 := fun h ↦ ⟨h.1, by
    refine Set.range_restrict .. ▸ ⟨⟨_, continuous_subtype_val.comp h.2.2⟩, ?_⟩
    simp_rw [ContinuousMap.coe_mk, ← Function.comp_assoc]
    exact ⟨(Equiv.comp_symm_eq ..).mpr rfl, by simp⟩⟩
  tfae_have 4 → 5 := fun h ↦ ⟨_, h⟩
  tfae_have 5 → 1 := by
    rintro ⟨U, hU, sec, hsec, rfl⟩
    exact ⟨(hf.isOpenEmbedding_section hU hsec sec.continuous).isOpen_range,
      Set.injOn_range_subtype_section hsec⟩
  tfae_finish

theorem isOpen_range_section_iff (hf : IsLocalHomeomorph f) {sec : t → X} (hsec : f ∘ sec = (↑)) :
    IsOpen (Set.range sec) ↔ IsOpen t ∧ Continuous sec := by
  have : f '' Set.range sec = t := by rw [← Set.range_comp, hsec, Subtype.range_val]
  convert ← (hf.isOpen_injOn_tfae (Set.range sec)).out 0 3
  · exact and_iff_left (Set.injOn_range_subtype_section hsec)
  refine this.symm ▸ ⟨fun ⟨⟨s, _⟩, hfs, eq⟩ ↦ ?_, fun h ↦ ⟨⟨_, h⟩, hsec, rfl⟩⟩
  rwa [← Set.subtype_section_ext hfs hsec eq]

theorem isOpenEmbedding_restrict (hf : IsLocalHomeomorph f) (hs : IsOpen s) (hsf : s.InjOn f) :
    IsOpenEmbedding (s.restrict f) :=
  isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨hf.continuous.comp continuous_subtype_val,
    hsf.injective, hf.isOpenMap.comp hs.isOpenMap_subtype_val⟩

theorem exists_section (hf : IsLocalHomeomorph f) (x : X) :
    ∃ U : Set Y, IsOpen U ∧ ∃ s : C(U, X), f ∘ s = (↑) ∧ ∃ h : f x ∈ U, s ⟨_, h⟩ = x := by
  have ⟨V, hxV, hfV⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x
  obtain ⟨U, hU, s, hs, rfl⟩ := ((hf.isOpen_injOn_tfae V).out 1 4).mp hfV
  obtain ⟨y, rfl⟩ := mem_of_mem_nhds hxV
  rw [← f.comp_apply, hs]
  exact ⟨U, hU, s, hs, y.2, rfl⟩

open TopologicalSpace in
/-- Ranges of continuous local sections of a local homeomorphism form a basis of
the source space. See `isOpen_injOn_tfae` for more characterizations of sets in the basis. -/
theorem isTopologicalBasis (hf : IsLocalHomeomorph f) : IsTopologicalBasis
    {U : Set X | ∃ V : Set Y, IsOpen V ∧ ∃ s : C(V,X), f ∘ s = (↑) ∧ Set.range s = U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU ↦ ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    exact (hf.isOpenEmbedding_section hU hs s.continuous).isOpen_range
  · have ⟨V, hV, hfV⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x
    have := ((hf.isOpen_injOn_tfae (V ∩ U)).out 1 4).mp <| hfV.comp
      (.inclusion Set.inter_subset_left <| by simpa using hU.preimage continuous_subtype_val)
    exact ⟨_, this, ⟨mem_of_mem_nhds hV, hx⟩, Set.inter_subset_right⟩

end IsLocalHomeomorph

theorem isLocalHomeomorph_iff_isLocallyInjective_continuous_isOpenMap :
    IsLocalHomeomorph f ↔ IsLocallyInjective f ∧ Continuous f ∧ IsOpenMap f where
  mp h := ⟨h.isLocallyInjective, h.continuous, h.isOpenMap⟩
  mpr h := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦
    have ⟨U, hU, hxU, inj⟩ := h.1 x
    ⟨U, hU.mem_nhds hxU, isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
      ⟨h.2.1.comp continuous_subtype_val, Set.injOn_iff_injective.mp inj, h.2.2.restrict hU⟩⟩
