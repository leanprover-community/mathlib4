/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Order

#align_import topology.maps from "leanprover-community/mathlib"@"d91e7f7a7f1c7e9f0e18fdb6bde4f652004c735d"

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `Inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `Embedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `OpenEmbedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `ClosedEmbedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `QuotientMap f` is the dual condition to `Embedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/


open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X → Y} {g : Y → Z}

section Inducing

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem inducing_induced (f : X → Y) : @Inducing X Y (TopologicalSpace.induced f ‹_›) _ f :=
  @Inducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

theorem inducing_id : Inducing (@id X) :=
  ⟨induced_id.symm⟩
#align inducing_id inducing_id

protected theorem Inducing.comp (hg : Inducing g) (hf : Inducing f) :
    Inducing (g ∘ f) :=
  ⟨by rw [hf.induced, hg.induced, induced_compose]⟩
#align inducing.comp Inducing.comp

theorem Inducing.of_comp_iff (hg : Inducing g) :
    Inducing (g ∘ f) ↔ Inducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [inducing_iff, hg.induced, induced_compose, h.induced]
#align inducing.inducing_iff Inducing.of_comp_iff

theorem inducing_of_inducing_compose
    (hf : Continuous f) (hg : Continuous g) (hgf : Inducing (g ∘ f)) : Inducing f :=
  ⟨le_antisymm (by rwa [← continuous_iff_le_induced])
      (by
        rw [hgf.induced, ← induced_compose]
        exact induced_mono hg.le_induced)⟩
#align inducing_of_inducing_compose inducing_of_inducing_compose

theorem inducing_iff_nhds : Inducing f ↔ ∀ x, 𝓝 x = comap f (𝓝 (f x)) :=
  (inducing_iff _).trans (induced_iff_nhds_eq f)
#align inducing_iff_nhds inducing_iff_nhds

namespace Inducing

theorem nhds_eq_comap (hf : Inducing f) : ∀ x : X, 𝓝 x = comap f (𝓝 <| f x) :=
  inducing_iff_nhds.1 hf
#align inducing.nhds_eq_comap Inducing.nhds_eq_comap

theorem basis_nhds {p : ι → Prop} {s : ι → Set Y} (hf : Inducing f) {x : X}
    (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s) :=
  hf.nhds_eq_comap x ▸ h_basis.comap f

theorem nhdsSet_eq_comap (hf : Inducing f) (s : Set X) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]
#align inducing.nhds_set_eq_comap Inducing.nhdsSet_eq_comap

theorem map_nhds_eq (hf : Inducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.induced.symm ▸ map_nhds_induced_eq x
#align inducing.map_nhds_eq Inducing.map_nhds_eq

theorem map_nhds_of_mem (hf : Inducing f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.induced.symm ▸ map_nhds_induced_of_mem h
#align inducing.map_nhds_of_mem Inducing.map_nhds_of_mem

-- Porting note (#10756): new lemma
theorem mapClusterPt_iff (hf : Inducing f) {x : X} {l : Filter X} :
    MapClusterPt (f x) l f ↔ ClusterPt x l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull', ← hf.nhds_eq_comap, map_neBot_iff]

theorem image_mem_nhdsWithin (hf : Inducing f) {x : X} {s : Set X} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝[range f] f x :=
  hf.map_nhds_eq x ▸ image_mem_map hs
#align inducing.image_mem_nhds_within Inducing.image_mem_nhdsWithin

theorem tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : Inducing g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]
#align inducing.tendsto_nhds_iff Inducing.tendsto_nhds_iff

theorem continuousAt_iff (hg : Inducing g) {x : X} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff
#align inducing.continuous_at_iff Inducing.continuousAt_iff

theorem continuous_iff (hg : Inducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]
#align inducing.continuous_iff Inducing.continuous_iff

theorem continuousAt_iff' (hf : Inducing f) {x : X} (h : range f ∈ 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]
#align inducing.continuous_at_iff' Inducing.continuousAt_iff'

protected theorem continuous (hf : Inducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id
#align inducing.continuous Inducing.continuous

theorem closure_eq_preimage_closure_image (hf : Inducing f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.induced]
#align inducing.closure_eq_preimage_closure_image Inducing.closure_eq_preimage_closure_image

theorem isClosed_iff (hf : Inducing f) {s : Set X} :
    IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.induced, isClosed_induced_iff]
#align inducing.is_closed_iff Inducing.isClosed_iff

theorem isClosed_iff' (hf : Inducing f) {s : Set X} :
    IsClosed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s := by rw [hf.induced, isClosed_induced_iff']
#align inducing.is_closed_iff' Inducing.isClosed_iff'

theorem isClosed_preimage (h : Inducing f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (isClosed_iff h).mpr ⟨s, hs, rfl⟩
#align inducing.is_closed_preimage Inducing.isClosed_preimage

theorem isOpen_iff (hf : Inducing f) {s : Set X} :
    IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.induced, isOpen_induced_iff]
#align inducing.is_open_iff Inducing.isOpen_iff

theorem setOf_isOpen (hf : Inducing f) :
    {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ ↦ hf.isOpen_iff

theorem dense_iff (hf : Inducing f) {s : Set X} :
    Dense s ↔ ∀ x, f x ∈ closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]
#align inducing.dense_iff Inducing.dense_iff

theorem of_subsingleton [Subsingleton X] (f : X → Y) : Inducing f :=
  ⟨Subsingleton.elim _ _⟩

end Inducing

end Inducing

section Embedding

theorem Function.Injective.embedding_induced [t : TopologicalSpace Y] (hf : Injective f) :
    @_root_.Embedding X Y (t.induced f) t f :=
  @_root_.Embedding.mk X Y (t.induced f) t _ (inducing_induced f) hf
#align function.injective.embedding_induced Function.Injective.embedding_induced

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem Embedding.mk' (f : X → Y) (inj : Injective f) (induced : ∀ x, comap f (𝓝 (f x)) = 𝓝 x) :
    Embedding f :=
  ⟨inducing_iff_nhds.2 fun x => (induced x).symm, inj⟩
#align embedding.mk' Embedding.mk'

theorem embedding_id : Embedding (@id X) :=
  ⟨inducing_id, fun _ _ h => h⟩
#align embedding_id embedding_id

protected theorem Embedding.comp (hg : Embedding g) (hf : Embedding f) :
    Embedding (g ∘ f) :=
  { hg.toInducing.comp hf.toInducing with inj := fun _ _ h => hf.inj <| hg.inj h }
#align embedding.comp Embedding.comp

theorem Embedding.of_comp_iff (hg : Embedding g) : Embedding (g ∘ f) ↔ Embedding f := by
  simp_rw [embedding_iff, hg.toInducing.of_comp_iff, hg.inj.of_comp_iff f]

theorem embedding_of_embedding_compose
    (hf : Continuous f) (hg : Continuous g) (hgf : Embedding (g ∘ f)) : Embedding f :=
  { induced := (inducing_of_inducing_compose hf hg hgf.toInducing).induced
    inj := fun x₁ x₂ h => hgf.inj <| by simp [h, (· ∘ ·)] }
#align embedding_of_embedding_compose embedding_of_embedding_compose

protected theorem Function.LeftInverse.embedding {f : X → Y} {g : Y → X} (h : LeftInverse f g)
    (hf : Continuous f) (hg : Continuous g) : _root_.Embedding g :=
  embedding_of_embedding_compose hg hf <| h.comp_eq_id.symm ▸ embedding_id
#align function.left_inverse.embedding Function.LeftInverse.embedding

theorem Embedding.map_nhds_eq (hf : Embedding f) (x : X) :
    (𝓝 x).map f = 𝓝[range f] f x :=
  hf.1.map_nhds_eq x
#align embedding.map_nhds_eq Embedding.map_nhds_eq

theorem Embedding.map_nhds_of_mem (hf : Embedding f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.1.map_nhds_of_mem x h
#align embedding.map_nhds_of_mem Embedding.map_nhds_of_mem

theorem Embedding.tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y}
    (hg : Embedding g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.toInducing.tendsto_nhds_iff
#align embedding.tendsto_nhds_iff Embedding.tendsto_nhds_iff

theorem Embedding.continuous_iff (hg : Embedding g) :
    Continuous f ↔ Continuous (g ∘ f) :=
  Inducing.continuous_iff hg.1
#align embedding.continuous_iff Embedding.continuous_iff

theorem Embedding.continuous (hf : Embedding f) : Continuous f :=
  Inducing.continuous hf.1
#align embedding.continuous Embedding.continuous

theorem Embedding.closure_eq_preimage_closure_image (hf : Embedding f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) :=
  hf.1.closure_eq_preimage_closure_image s
#align embedding.closure_eq_preimage_closure_image Embedding.closure_eq_preimage_closure_image

/-- The topology induced under an inclusion `f : X → Y` from a discrete topological space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`. -/
theorem Embedding.discreteTopology [DiscreteTopology Y] (hf : Embedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.inj
#align embedding.discrete_topology Embedding.discreteTopology

theorem Embedding.of_subsingleton [Subsingleton X] (f : X → Y) : Embedding f :=
  ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

end Embedding

section QuotientMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem quotientMap_iff : QuotientMap f ↔ Surjective f ∧ ∀ s : Set Y, IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  and_congr Iff.rfl TopologicalSpace.ext_iff
#align quotient_map_iff quotientMap_iff

theorem quotientMap_iff_closed :
    QuotientMap f ↔ Surjective f ∧ ∀ s : Set Y, IsClosed s ↔ IsClosed (f ⁻¹' s) :=
  quotientMap_iff.trans <| Iff.rfl.and <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]
#align quotient_map_iff_closed quotientMap_iff_closed

namespace QuotientMap

protected theorem id : QuotientMap (@id X) :=
  ⟨fun x => ⟨x, rfl⟩, coinduced_id.symm⟩
#align quotient_map.id QuotientMap.id

protected theorem comp (hg : QuotientMap g) (hf : QuotientMap f) : QuotientMap (g ∘ f) :=
  ⟨hg.left.comp hf.left, by rw [hg.right, hf.right, coinduced_compose]⟩
#align quotient_map.comp QuotientMap.comp

protected theorem of_quotientMap_compose (hf : Continuous f) (hg : Continuous g)
    (hgf : QuotientMap (g ∘ f)) : QuotientMap g :=
  ⟨hgf.1.of_comp,
    le_antisymm
      (by rw [hgf.right, ← coinduced_compose]; exact coinduced_mono hf.coinduced_le)
      hg.coinduced_le⟩
#align quotient_map.of_quotient_map_compose QuotientMap.of_quotientMap_compose

theorem of_inverse {g : Y → X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
    QuotientMap g :=
  QuotientMap.of_quotientMap_compose hf hg <| h.comp_eq_id.symm ▸ QuotientMap.id
#align quotient_map.of_inverse QuotientMap.of_inverse

protected theorem continuous_iff (hf : QuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]
#align quotient_map.continuous_iff QuotientMap.continuous_iff

protected theorem continuous (hf : QuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id
#align quotient_map.continuous QuotientMap.continuous

protected theorem surjective (hf : QuotientMap f) : Surjective f :=
  hf.1
#align quotient_map.surjective QuotientMap.surjective

protected theorem isOpen_preimage (hf : QuotientMap f) {s : Set Y} : IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  ((quotientMap_iff.1 hf).2 s).symm
#align quotient_map.is_open_preimage QuotientMap.isOpen_preimage

protected theorem isClosed_preimage (hf : QuotientMap f) {s : Set Y} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  ((quotientMap_iff_closed.1 hf).2 s).symm
#align quotient_map.is_closed_preimage QuotientMap.isClosed_preimage

end QuotientMap

end QuotientMap

section OpenMap
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsOpenMap

protected theorem id : IsOpenMap (@id X) := fun s hs => by rwa [image_id]
#align is_open_map.id IsOpenMap.id

protected theorem comp (hg : IsOpenMap g) (hf : IsOpenMap f) :
    IsOpenMap (g ∘ f) := fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)
#align is_open_map.comp IsOpenMap.comp

theorem isOpen_range (hf : IsOpenMap f) : IsOpen (range f) := by
  rw [← image_univ]
  exact hf _ isOpen_univ
#align is_open_map.is_open_range IsOpenMap.isOpen_range

theorem image_mem_nhds (hf : IsOpenMap f) {x : X} {s : Set X} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)
#align is_open_map.image_mem_nhds IsOpenMap.image_mem_nhds

theorem range_mem_nhds (hf : IsOpenMap f) (x : X) : range f ∈ 𝓝 (f x) :=
  hf.isOpen_range.mem_nhds <| mem_range_self _
#align is_open_map.range_mem_nhds IsOpenMap.range_mem_nhds

theorem mapsTo_interior (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
  mapsTo'.2 <|
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)
#align is_open_map.maps_to_interior IsOpenMap.mapsTo_interior

theorem image_interior_subset (hf : IsOpenMap f) (s : Set X) :
    f '' interior s ⊆ interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset
#align is_open_map.image_interior_subset IsOpenMap.image_interior_subset

theorem nhds_le (hf : IsOpenMap f) (x : X) : 𝓝 (f x) ≤ (𝓝 x).map f :=
  le_map fun _ => hf.image_mem_nhds
#align is_open_map.nhds_le IsOpenMap.nhds_le

theorem of_nhds_le (hf : ∀ x, 𝓝 (f x) ≤ map f (𝓝 x)) : IsOpenMap f := fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)
#align is_open_map.of_nhds_le IsOpenMap.of_nhds_le

theorem of_sections
    (h : ∀ x, ∃ g : Y → X, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) : IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ ≤ map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]
#align is_open_map.of_sections IsOpenMap.of_sections

theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsOpenMap f :=
  of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩
#align is_open_map.of_inverse IsOpenMap.of_inverse

/-- A continuous surjective open map is a quotient map. -/
theorem to_quotientMap (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f) :
    QuotientMap f :=
  quotientMap_iff.2
    ⟨surj, fun s => ⟨fun h => h.preimage cont, fun h => surj.image_preimage s ▸ open_map _ h⟩⟩
#align is_open_map.to_quotient_map IsOpenMap.to_quotientMap

theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set Y} :
    interior (f ⁻¹' s) ⊆ f ⁻¹' interior s :=
  hf.mapsTo_interior (mapsTo_preimage _ _)
#align is_open_map.interior_preimage_subset_preimage_interior IsOpenMap.interior_preimage_subset_preimage_interior

theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
    (s : Set Y) : f ⁻¹' interior s = interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)
#align is_open_map.preimage_interior_eq_interior_preimage IsOpenMap.preimage_interior_eq_interior_preimage

theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' closure s ⊆ closure (f ⁻¹' s) := by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]
#align is_open_map.preimage_closure_subset_closure_preimage IsOpenMap.preimage_closure_subset_closure_preimage

theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' closure s = closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)
#align is_open_map.preimage_closure_eq_closure_preimage IsOpenMap.preimage_closure_eq_closure_preimage

theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' frontier s ⊆ frontier (f ⁻¹' s) := by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage
#align is_open_map.preimage_frontier_subset_frontier_preimage IsOpenMap.preimage_frontier_subset_frontier_preimage

theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' frontier s = frontier (f ⁻¹' s) := by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]
#align is_open_map.preimage_frontier_eq_frontier_preimage IsOpenMap.preimage_frontier_eq_frontier_preimage

theorem of_isEmpty [h : IsEmpty X] (f : X → Y) : IsOpenMap f := of_nhds_le h.elim

end IsOpenMap

theorem isOpenMap_iff_nhds_le : IsOpenMap f ↔ ∀ x : X, 𝓝 (f x) ≤ (𝓝 x).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩
#align is_open_map_iff_nhds_le isOpenMap_iff_nhds_le

theorem isOpenMap_iff_interior : IsOpenMap f ↔ ∀ s, f '' interior s ⊆ interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_isOpen.mp <|
      calc
        f '' u = f '' interior u := by rw [hu.interior_eq]
        _ ⊆ interior (f '' u) := hs u⟩
#align is_open_map_iff_interior isOpenMap_iff_interior

/-- An inducing map with an open range is an open map. -/
protected theorem Inducing.isOpenMap (hi : Inducing f) (ho : IsOpen (range f)) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge
#align inducing.is_open_map Inducing.isOpenMap

end OpenMap

section IsClosedMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedMap
open Function

protected theorem id : IsClosedMap (@id X) := fun s hs => by rwa [image_id]
#align is_closed_map.id IsClosedMap.id

protected theorem comp (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)
#align is_closed_map.comp IsClosedMap.comp

theorem closure_image_subset (hf : IsClosedMap f) (s : Set X) :
    closure (f '' s) ⊆ f '' closure s :=
  closure_minimal (image_subset _ subset_closure) (hf _ isClosed_closure)
#align is_closed_map.closure_image_subset IsClosedMap.closure_image_subset

theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsClosedMap f := fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h
#align is_closed_map.of_inverse IsClosedMap.of_inverse

theorem of_nonempty (h : ∀ s, IsClosed s → s.Nonempty → IsClosed (f '' s)) :
    IsClosedMap f := by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s
#align is_closed_map.of_nonempty IsClosedMap.of_nonempty

theorem isClosed_range (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ isClosed_univ
#align is_closed_map.closed_range IsClosedMap.isClosed_range

@[deprecated (since := "2024-03-17")] alias closed_range := isClosed_range

theorem to_quotientMap (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : QuotientMap f :=
  quotientMap_iff_closed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩
#align is_closed_map.to_quotient_map IsClosedMap.to_quotientMap

end IsClosedMap

theorem Inducing.isClosedMap (hf : Inducing f) (h : IsClosed (range f)) : IsClosedMap f := by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h
#align inducing.is_closed_map Inducing.isClosedMap

theorem isClosedMap_iff_closure_image :
    IsClosedMap f ↔ ∀ s, closure (f '' s) ⊆ f '' closure s :=
  ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
    isClosed_of_closure_subset <|
      calc
        closure (f '' c) ⊆ f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩
#align is_closed_map_iff_closure_image isClosedMap_iff_closure_image

/-- A map `f : X → Y` is closed if and only if for all sets `s`, any cluster point of `f '' s` is
the image by `f` of some cluster point of `s`.
If you require this for all filters instead of just principal filters, and also that `f` is
continuous, you get the notion of **proper map**. See `isProperMap_iff_clusterPt`. -/
theorem isClosedMap_iff_clusterPt :
    IsClosedMap f ↔ ∀ s y, MapClusterPt y (𝓟 s) f → ∃ x, f x = y ∧ ClusterPt x (𝓟 s) := by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

theorem IsClosedMap.closure_image_eq_of_continuous
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

theorem IsClosedMap.lift'_closure_map_eq
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter X) :
    (map f F).lift' closure = map f (F.lift' closure) := by
  rw [map_lift'_eq2 (monotone_closure Y), map_lift'_eq (monotone_closure X)]
  congr
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

theorem IsClosedMap.mapClusterPt_iff_lift'_closure
    {F : Filter X} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : Y} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt, clusterPt_iff_lift'_closure', f_closed.lift'_closure_map_eq f_cont,
      ← comap_principal, ← map_neBot_iff f, Filter.push_pull, principal_singleton]

end IsClosedMap

section OpenEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem OpenEmbedding.isOpenMap (hf : OpenEmbedding f) : IsOpenMap f :=
  hf.toEmbedding.toInducing.isOpenMap hf.isOpen_range
#align open_embedding.is_open_map OpenEmbedding.isOpenMap

theorem OpenEmbedding.map_nhds_eq (hf : OpenEmbedding f) (x : X) :
    map f (𝓝 x) = 𝓝 (f x) :=
  hf.toEmbedding.map_nhds_of_mem _ <| hf.isOpen_range.mem_nhds <| mem_range_self _
#align open_embedding.map_nhds_eq OpenEmbedding.map_nhds_eq

theorem OpenEmbedding.open_iff_image_open (hf : OpenEmbedding f) {s : Set X} :
    IsOpen s ↔ IsOpen (f '' s) :=
  ⟨hf.isOpenMap s, fun h => by
    convert ← h.preimage hf.toEmbedding.continuous
    apply preimage_image_eq _ hf.inj⟩
#align open_embedding.open_iff_image_open OpenEmbedding.open_iff_image_open

theorem OpenEmbedding.tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : OpenEmbedding g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.toEmbedding.tendsto_nhds_iff
#align open_embedding.tendsto_nhds_iff OpenEmbedding.tendsto_nhds_iff

theorem OpenEmbedding.tendsto_nhds_iff' (hf : OpenEmbedding f) {l : Filter Z} {x : X} :
    Tendsto (g ∘ f) (𝓝 x) l ↔ Tendsto g (𝓝 (f x)) l := by
  rw [Tendsto, ← map_map, hf.map_nhds_eq]; rfl

theorem OpenEmbedding.continuousAt_iff (hf : OpenEmbedding f) {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'
#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iff

theorem OpenEmbedding.continuous (hf : OpenEmbedding f) : Continuous f :=
  hf.toEmbedding.continuous
#align open_embedding.continuous OpenEmbedding.continuous

theorem OpenEmbedding.open_iff_preimage_open (hf : OpenEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.open_iff_image_open, image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]
#align open_embedding.open_iff_preimage_open OpenEmbedding.open_iff_preimage_open

theorem openEmbedding_of_embedding_open (h₁ : Embedding f) (h₂ : IsOpenMap f) :
    OpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩
#align open_embedding_of_embedding_open openEmbedding_of_embedding_open

/-- A surjective embedding is an `OpenEmbedding`. -/
theorem _root_.Embedding.toOpenEmbedding_of_surjective (hf : Embedding f) (hsurj: f.Surjective) :
    OpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

theorem openEmbedding_iff_embedding_open :
    OpenEmbedding f ↔ Embedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => openEmbedding_of_embedding_open h.1 h.2⟩
#align open_embedding_iff_embedding_open openEmbedding_iff_embedding_open

theorem openEmbedding_of_continuous_injective_open
    (h₁ : Continuous f) (h₂ : Injective f) (h₃ : IsOpenMap f) : OpenEmbedding f := by
  simp only [openEmbedding_iff_embedding_open, embedding_iff, inducing_iff_nhds, *, and_true_iff]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))
#align open_embedding_of_continuous_injective_open openEmbedding_of_continuous_injective_open

theorem openEmbedding_iff_continuous_injective_open :
    OpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.inj, h.isOpenMap⟩, fun h =>
    openEmbedding_of_continuous_injective_open h.1 h.2.1 h.2.2⟩
#align open_embedding_iff_continuous_injective_open openEmbedding_iff_continuous_injective_open

theorem openEmbedding_id : OpenEmbedding (@id X) :=
  ⟨embedding_id, IsOpenMap.id.isOpen_range⟩
#align open_embedding_id openEmbedding_id

namespace OpenEmbedding

protected theorem comp (hg : OpenEmbedding g)
    (hf : OpenEmbedding f) : OpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩
#align open_embedding.comp OpenEmbedding.comp

theorem isOpenMap_iff (hg : OpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, Filter.map_le_map_iff hg.inj]
#align open_embedding.is_open_map_iff OpenEmbedding.isOpenMap_iff

theorem of_comp_iff (f : X → Y) (hg : OpenEmbedding g) :
    OpenEmbedding (g ∘ f) ↔ OpenEmbedding f := by
  simp only [openEmbedding_iff_continuous_injective_open, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.inj.of_comp_iff]
#align open_embedding.of_comp_iff OpenEmbedding.of_comp_iff

theorem of_comp (f : X → Y) (hg : OpenEmbedding g)
    (h : OpenEmbedding (g ∘ f)) : OpenEmbedding f :=
  (OpenEmbedding.of_comp_iff f hg).1 h
#align open_embedding.of_comp OpenEmbedding.of_comp

theorem of_isEmpty [IsEmpty X] (f : X → Y) : OpenEmbedding f :=
  openEmbedding_of_embedding_open (.of_subsingleton f) (IsOpenMap.of_isEmpty f)

end OpenEmbedding

end OpenEmbedding

section ClosedEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace ClosedEmbedding

theorem tendsto_nhds_iff {g : ι → X} {l : Filter ι} {x : X} (hf : ClosedEmbedding f) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) :=
  hf.toEmbedding.tendsto_nhds_iff
#align closed_embedding.tendsto_nhds_iff ClosedEmbedding.tendsto_nhds_iff

theorem continuous (hf : ClosedEmbedding f) : Continuous f :=
  hf.toEmbedding.continuous
#align closed_embedding.continuous ClosedEmbedding.continuous

theorem isClosedMap (hf : ClosedEmbedding f) : IsClosedMap f :=
  hf.toEmbedding.toInducing.isClosedMap hf.isClosed_range
#align closed_embedding.is_closed_map ClosedEmbedding.isClosedMap

theorem closed_iff_image_closed (hf : ClosedEmbedding f) {s : Set X} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.inj]
    exact h.preimage hf.continuous⟩
#align closed_embedding.closed_iff_image_closed ClosedEmbedding.closed_iff_image_closed

theorem closed_iff_preimage_closed (hf : ClosedEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.closed_iff_image_closed, image_preimage_eq_of_subset hs]
#align closed_embedding.closed_iff_preimage_closed ClosedEmbedding.closed_iff_preimage_closed

theorem _root_.closedEmbedding_of_embedding_closed (h₁ : Embedding f) (h₂ : IsClosedMap f) :
    ClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩
#align closed_embedding_of_embedding_closed closedEmbedding_of_embedding_closed

theorem _root_.closedEmbedding_of_continuous_injective_closed (h₁ : Continuous f) (h₂ : Injective f)
    (h₃ : IsClosedMap f) : ClosedEmbedding f := by
  refine closedEmbedding_of_embedding_closed ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl, preimage_image_eq _ h₂, compl_compl]
#align closed_embedding_of_continuous_injective_closed closedEmbedding_of_continuous_injective_closed

theorem _root_.closedEmbedding_id : ClosedEmbedding (@id X) :=
  ⟨embedding_id, IsClosedMap.id.isClosed_range⟩
#align closed_embedding_id closedEmbedding_id

theorem comp (hg : ClosedEmbedding g) (hf : ClosedEmbedding f) :
    ClosedEmbedding (g ∘ f) :=
  ⟨hg.toEmbedding.comp hf.toEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩
#align closed_embedding.comp ClosedEmbedding.comp

theorem of_comp_iff (hg : ClosedEmbedding g) :
    ClosedEmbedding (g ∘ f) ↔ ClosedEmbedding f := by
  simp_rw [closedEmbedding_iff, hg.toEmbedding.of_comp_iff, Set.range_comp,
    ← hg.closed_iff_image_closed]

theorem closure_image_eq (hf : ClosedEmbedding f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s
#align closed_embedding.closure_image_eq ClosedEmbedding.closure_image_eq

end ClosedEmbedding

end ClosedEmbedding
