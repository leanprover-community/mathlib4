/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Order
import Mathlib.Topology.NhdsSet

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

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section Inducing

/-- A function `f : α → β` between topological spaces is inducing if the topology on `α` is induced
by the topology on `β` through `f`, meaning that a set `s : Set α` is open iff it is the preimage
under `f` of some open set `t : Set β`. -/
@[mk_iff]
structure Inducing [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  induced : tα = tβ.induced f
#align inducing Inducing
#align inducing_iff inducing_iff

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

theorem inducing_induced (f : α → β) : @Inducing α β (TopologicalSpace.induced f ‹_›) _ f :=
  @Inducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

theorem inducing_id : Inducing (@id α) :=
  ⟨induced_id.symm⟩
#align inducing_id inducing_id

protected theorem Inducing.comp {g : β → γ} {f : α → β} (hg : Inducing g) (hf : Inducing f) :
    Inducing (g ∘ f) :=
  ⟨by rw [hf.induced, hg.induced, induced_compose]⟩
#align inducing.comp Inducing.comp

theorem inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
    (hgf : Inducing (g ∘ f)) : Inducing f :=
  ⟨le_antisymm (by rwa [← continuous_iff_le_induced])
      (by
        rw [hgf.induced, ← induced_compose]
        exact induced_mono hg.le_induced)⟩
#align inducing_of_inducing_compose inducing_of_inducing_compose

theorem inducing_iff_nhds {f : α → β} : Inducing f ↔ ∀ a, 𝓝 a = comap f (𝓝 (f a)) :=
  (inducing_iff _).trans (induced_iff_nhds_eq f)
#align inducing_iff_nhds inducing_iff_nhds

theorem Inducing.nhds_eq_comap {f : α → β} (hf : Inducing f) : ∀ a : α, 𝓝 a = comap f (𝓝 <| f a) :=
  inducing_iff_nhds.1 hf
#align inducing.nhds_eq_comap Inducing.nhds_eq_comap

theorem Inducing.nhdsSet_eq_comap {f : α → β} (hf : Inducing f) (s : Set α) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]
#align inducing.nhds_set_eq_comap Inducing.nhdsSet_eq_comap

theorem Inducing.map_nhds_eq {f : α → β} (hf : Inducing f) (a : α) : (𝓝 a).map f = 𝓝[range f] f a :=
  hf.induced.symm ▸ map_nhds_induced_eq a
#align inducing.map_nhds_eq Inducing.map_nhds_eq

theorem Inducing.map_nhds_of_mem {f : α → β} (hf : Inducing f) (a : α) (h : range f ∈ 𝓝 (f a)) :
    (𝓝 a).map f = 𝓝 (f a) :=
  hf.induced.symm ▸ map_nhds_induced_of_mem h
#align inducing.map_nhds_of_mem Inducing.map_nhds_of_mem

-- porting note: new lemma
theorem Inducing.mapClusterPt_iff {f : α → β} (hf : Inducing f) {a : α} {l : Filter α} :
    MapClusterPt (f a) l f ↔ ClusterPt a l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull', ← hf.nhds_eq_comap, map_neBot_iff]

theorem Inducing.image_mem_nhdsWithin {f : α → β} (hf : Inducing f) {a : α} {s : Set α}
    (hs : s ∈ 𝓝 a) : f '' s ∈ 𝓝[range f] f a :=
  hf.map_nhds_eq a ▸ image_mem_map hs
#align inducing.image_mem_nhds_within Inducing.image_mem_nhdsWithin

theorem Inducing.tendsto_nhds_iff {ι : Type*} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β}
    (hg : Inducing g) : Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]
#align inducing.tendsto_nhds_iff Inducing.tendsto_nhds_iff

theorem Inducing.continuousAt_iff {f : α → β} {g : β → γ} (hg : Inducing g) {x : α} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff
#align inducing.continuous_at_iff Inducing.continuousAt_iff

theorem Inducing.continuous_iff {f : α → β} {g : β → γ} (hg : Inducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]
#align inducing.continuous_iff Inducing.continuous_iff

theorem Inducing.continuousAt_iff' {f : α → β} {g : β → γ} (hf : Inducing f) {x : α}
    (h : range f ∈ 𝓝 (f x)) : ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]
#align inducing.continuous_at_iff' Inducing.continuousAt_iff'

protected theorem Inducing.continuous {f : α → β} (hf : Inducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id
#align inducing.continuous Inducing.continuous

protected theorem Inducing.inducing_iff {f : α → β} {g : β → γ} (hg : Inducing g) :
    Inducing f ↔ Inducing (g ∘ f) := by
  refine' ⟨fun h => hg.comp h, fun hgf => inducing_of_inducing_compose _ hg.continuous hgf⟩
  rw [hg.continuous_iff]
  exact hgf.continuous
#align inducing.inducing_iff Inducing.inducing_iff

theorem Inducing.closure_eq_preimage_closure_image {f : α → β} (hf : Inducing f) (s : Set α) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.induced]
#align inducing.closure_eq_preimage_closure_image Inducing.closure_eq_preimage_closure_image

theorem Inducing.isClosed_iff {f : α → β} (hf : Inducing f) {s : Set α} :
    IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.induced, isClosed_induced_iff]
#align inducing.is_closed_iff Inducing.isClosed_iff

theorem Inducing.isClosed_iff' {f : α → β} (hf : Inducing f) {s : Set α} :
    IsClosed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s := by rw [hf.induced, isClosed_induced_iff']
#align inducing.is_closed_iff' Inducing.isClosed_iff'

theorem Inducing.isClosed_preimage {f : α → β} (h : Inducing f) (s : Set β) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (Inducing.isClosed_iff h).mpr ⟨s, hs, rfl⟩
#align inducing.is_closed_preimage Inducing.isClosed_preimage

theorem Inducing.isOpen_iff {f : α → β} (hf : Inducing f) {s : Set α} :
    IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.induced, isOpen_induced_iff]
#align inducing.is_open_iff Inducing.isOpen_iff

theorem Inducing.setOf_isOpen {f : α → β} (hf : Inducing f) :
    {s : Set α | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ ↦ hf.isOpen_iff

theorem Inducing.dense_iff {f : α → β} (hf : Inducing f) {s : Set α} :
    Dense s ↔ ∀ x, f x ∈ closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]
#align inducing.dense_iff Inducing.dense_iff

end Inducing

section Embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set α`, `s` is open iff it is the preimage of an open set. -/
@[mk_iff]
structure Embedding [TopologicalSpace α] [TopologicalSpace β] (f : α → β) extends
  Inducing f : Prop where
  /-- A topological embedding is injective. -/
  inj : Injective f
#align embedding Embedding
#align embedding_iff embedding_iff

theorem Function.Injective.embedding_induced [t : TopologicalSpace β] {f : α → β}
    (hf : Injective f) : @_root_.Embedding α β (t.induced f) t f :=
  @_root_.Embedding.mk α β (t.induced f) t _ (inducing_induced f) hf
#align function.injective.embedding_induced Function.Injective.embedding_induced

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem Embedding.mk' (f : α → β) (inj : Injective f) (induced : ∀ a, comap f (𝓝 (f a)) = 𝓝 a) :
    Embedding f :=
  ⟨inducing_iff_nhds.2 fun a => (induced a).symm, inj⟩
#align embedding.mk' Embedding.mk'

theorem embedding_id : Embedding (@id α) :=
  ⟨inducing_id, fun _ _ h => h⟩
#align embedding_id embedding_id

protected theorem Embedding.comp {g : β → γ} {f : α → β} (hg : Embedding g) (hf : Embedding f) :
    Embedding (g ∘ f) :=
  { hg.toInducing.comp hf.toInducing with inj := fun _ _ h => hf.inj <| hg.inj h }
#align embedding.comp Embedding.comp

theorem embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : Continuous f)
    (hg : Continuous g) (hgf : Embedding (g ∘ f)) : Embedding f :=
  { induced := (inducing_of_inducing_compose hf hg hgf.toInducing).induced
    inj := fun a₁ a₂ h => hgf.inj <| by simp [h, (· ∘ ·)] }
#align embedding_of_embedding_compose embedding_of_embedding_compose

protected theorem Function.LeftInverse.embedding {f : α → β} {g : β → α} (h : LeftInverse f g)
    (hf : Continuous f) (hg : Continuous g) : _root_.Embedding g :=
  embedding_of_embedding_compose hg hf <| h.comp_eq_id.symm ▸ embedding_id
#align function.left_inverse.embedding Function.LeftInverse.embedding

theorem Embedding.map_nhds_eq {f : α → β} (hf : Embedding f) (a : α) :
    (𝓝 a).map f = 𝓝[range f] f a :=
  hf.1.map_nhds_eq a
#align embedding.map_nhds_eq Embedding.map_nhds_eq

theorem Embedding.map_nhds_of_mem {f : α → β} (hf : Embedding f) (a : α) (h : range f ∈ 𝓝 (f a)) :
    (𝓝 a).map f = 𝓝 (f a) :=
  hf.1.map_nhds_of_mem a h
#align embedding.map_nhds_of_mem Embedding.map_nhds_of_mem

theorem Embedding.tendsto_nhds_iff {ι : Type*} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β}
    (hg : Embedding g) : Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.toInducing.tendsto_nhds_iff
#align embedding.tendsto_nhds_iff Embedding.tendsto_nhds_iff

theorem Embedding.continuous_iff {f : α → β} {g : β → γ} (hg : Embedding g) :
    Continuous f ↔ Continuous (g ∘ f) :=
  Inducing.continuous_iff hg.1
#align embedding.continuous_iff Embedding.continuous_iff

theorem Embedding.continuous {f : α → β} (hf : Embedding f) : Continuous f :=
  Inducing.continuous hf.1
#align embedding.continuous Embedding.continuous

theorem Embedding.closure_eq_preimage_closure_image {e : α → β} (he : Embedding e) (s : Set α) :
    closure s = e ⁻¹' closure (e '' s) :=
  he.1.closure_eq_preimage_closure_image s
#align embedding.closure_eq_preimage_closure_image Embedding.closure_eq_preimage_closure_image

/-- The topology induced under an inclusion `f : X → Y` from a discrete topological space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`. -/
theorem Embedding.discreteTopology {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f : X → Y} (hf : Embedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.inj
#align embedding.discrete_topology Embedding.discreteTopology

end Embedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set β`, `s` is open iff its preimage is an open set. -/
def QuotientMap {α : Type*} {β : Type*} [tα : TopologicalSpace α] [tβ : TopologicalSpace β]
    (f : α → β) : Prop :=
  Surjective f ∧ tβ = tα.coinduced f
#align quotient_map QuotientMap

theorem quotientMap_iff [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    QuotientMap f ↔ Surjective f ∧ ∀ s : Set β, IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  and_congr Iff.rfl TopologicalSpace.ext_iff
#align quotient_map_iff quotientMap_iff

theorem quotientMap_iff_closed [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    QuotientMap f ↔ Surjective f ∧ ∀ s : Set β, IsClosed s ↔ IsClosed (f ⁻¹' s) :=
  quotientMap_iff.trans <| Iff.rfl.and <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]
#align quotient_map_iff_closed quotientMap_iff_closed

namespace QuotientMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
  {g : β → γ} {f : α → β}

protected theorem id : QuotientMap (@id α) :=
  ⟨fun a => ⟨a, rfl⟩, coinduced_id.symm⟩
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

theorem of_inverse {g : β → α} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
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

protected theorem isOpen_preimage (hf : QuotientMap f) {s : Set β} : IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  ((quotientMap_iff.1 hf).2 s).symm
#align quotient_map.is_open_preimage QuotientMap.isOpen_preimage

protected theorem isClosed_preimage (hf : QuotientMap f) {s : Set β} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  ((quotientMap_iff_closed.1 hf).2 s).symm
#align quotient_map.is_closed_preimage QuotientMap.isClosed_preimage

end QuotientMap

/-- A map `f : α → β` is said to be an *open map*, if the image of any open `U : Set α`
is open in `β`. -/
def IsOpenMap [TopologicalSpace α] [TopologicalSpace β] (f : α → β) :=
  ∀ U : Set α, IsOpen U → IsOpen (f '' U)
#align is_open_map IsOpenMap

namespace IsOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β}

protected theorem id : IsOpenMap (@id α) := fun s hs => by rwa [image_id]
#align is_open_map.id IsOpenMap.id

protected theorem comp {g : β → γ} {f : α → β} (hg : IsOpenMap g) (hf : IsOpenMap f) :
    IsOpenMap (g ∘ f) := fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)
#align is_open_map.comp IsOpenMap.comp

theorem isOpen_range (hf : IsOpenMap f) : IsOpen (range f) := by
  rw [← image_univ]
  exact hf _ isOpen_univ
#align is_open_map.is_open_range IsOpenMap.isOpen_range

theorem image_mem_nhds (hf : IsOpenMap f) {x : α} {s : Set α} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)
#align is_open_map.image_mem_nhds IsOpenMap.image_mem_nhds

theorem range_mem_nhds (hf : IsOpenMap f) (x : α) : range f ∈ 𝓝 (f x) :=
  hf.isOpen_range.mem_nhds <| mem_range_self _
#align is_open_map.range_mem_nhds IsOpenMap.range_mem_nhds

theorem mapsTo_interior (hf : IsOpenMap f) {s : Set α} {t : Set β} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
  mapsTo'.2 <|
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)
#align is_open_map.maps_to_interior IsOpenMap.mapsTo_interior

theorem image_interior_subset (hf : IsOpenMap f) (s : Set α) :
    f '' interior s ⊆ interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset
#align is_open_map.image_interior_subset IsOpenMap.image_interior_subset

theorem nhds_le (hf : IsOpenMap f) (a : α) : 𝓝 (f a) ≤ (𝓝 a).map f :=
  le_map fun _ => hf.image_mem_nhds
#align is_open_map.nhds_le IsOpenMap.nhds_le

theorem of_nhds_le (hf : ∀ a, 𝓝 (f a) ≤ map f (𝓝 a)) : IsOpenMap f := fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _b ⟨_a, has, hab⟩ => hab ▸ hf _ (image_mem_map <| hs.mem_nhds has)
#align is_open_map.of_nhds_le IsOpenMap.of_nhds_le

theorem of_sections {f : α → β}
    (h : ∀ x, ∃ g : β → α, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) : IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ ≤ map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]
#align is_open_map.of_sections IsOpenMap.of_sections

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsOpenMap f :=
  of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩
#align is_open_map.of_inverse IsOpenMap.of_inverse

/-- A continuous surjective open map is a quotient map. -/
theorem to_quotientMap {f : α → β} (open_map : IsOpenMap f) (cont : Continuous f)
    (surj : Surjective f) : QuotientMap f :=
  quotientMap_iff.2
    ⟨surj, fun s => ⟨fun h => h.preimage cont, fun h => surj.image_preimage s ▸ open_map _ h⟩⟩
#align is_open_map.to_quotient_map IsOpenMap.to_quotientMap

theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set β} :
    interior (f ⁻¹' s) ⊆ f ⁻¹' interior s :=
  hf.mapsTo_interior (mapsTo_preimage _ _)
#align is_open_map.interior_preimage_subset_preimage_interior IsOpenMap.interior_preimage_subset_preimage_interior

theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
    (s : Set β) : f ⁻¹' interior s = interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)
#align is_open_map.preimage_interior_eq_interior_preimage IsOpenMap.preimage_interior_eq_interior_preimage

theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set β} :
    f ⁻¹' closure s ⊆ closure (f ⁻¹' s) := by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]
#align is_open_map.preimage_closure_subset_closure_preimage IsOpenMap.preimage_closure_subset_closure_preimage

theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set β) :
    f ⁻¹' closure s = closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)
#align is_open_map.preimage_closure_eq_closure_preimage IsOpenMap.preimage_closure_eq_closure_preimage

theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set β} :
    f ⁻¹' frontier s ⊆ frontier (f ⁻¹' s) := by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage
#align is_open_map.preimage_frontier_subset_frontier_preimage IsOpenMap.preimage_frontier_subset_frontier_preimage

theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set β) :
    f ⁻¹' frontier s = frontier (f ⁻¹' s) := by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]
#align is_open_map.preimage_frontier_eq_frontier_preimage IsOpenMap.preimage_frontier_eq_frontier_preimage

end IsOpenMap

theorem isOpenMap_iff_nhds_le [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsOpenMap f ↔ ∀ a : α, 𝓝 (f a) ≤ (𝓝 a).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩
#align is_open_map_iff_nhds_le isOpenMap_iff_nhds_le

theorem isOpenMap_iff_interior [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsOpenMap f ↔ ∀ s, f '' interior s ⊆ interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_isOpen.mp <|
      calc
        f '' u = f '' interior u := by rw [hu.interior_eq]
        _ ⊆ interior (f '' u) := hs u⟩
#align is_open_map_iff_interior isOpenMap_iff_interior

/-- An inducing map with an open range is an open map. -/
protected theorem Inducing.isOpenMap [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hi : Inducing f) (ho : IsOpen (range f)) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge
#align inducing.is_open_map Inducing.isOpenMap

section IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A map `f : α → β` is said to be a *closed map*, if the image of any closed `U : Set α`
is closed in `β`. -/
def IsClosedMap (f : α → β) :=
  ∀ U : Set α, IsClosed U → IsClosed (f '' U)
#align is_closed_map IsClosedMap

end IsClosedMap

namespace IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open Function

protected theorem id : IsClosedMap (@id α) := fun s hs => by rwa [image_id]
#align is_closed_map.id IsClosedMap.id

protected theorem comp {g : β → γ} {f : α → β} (hg : IsClosedMap g) (hf : IsClosedMap f) :
    IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)
#align is_closed_map.comp IsClosedMap.comp

theorem closure_image_subset {f : α → β} (hf : IsClosedMap f) (s : Set α) :
    closure (f '' s) ⊆ f '' closure s :=
  closure_minimal (image_subset _ subset_closure) (hf _ isClosed_closure)
#align is_closed_map.closure_image_subset IsClosedMap.closure_image_subset

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsClosedMap f := fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h
#align is_closed_map.of_inverse IsClosedMap.of_inverse

theorem of_nonempty {f : α → β} (h : ∀ s, IsClosed s → s.Nonempty → IsClosed (f '' s)) :
    IsClosedMap f := by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s
#align is_closed_map.of_nonempty IsClosedMap.of_nonempty

theorem closed_range {f : α → β} (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ isClosed_univ
#align is_closed_map.closed_range IsClosedMap.closed_range

theorem to_quotientMap {f : α → β} (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : QuotientMap f :=
  quotientMap_iff_closed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩
#align is_closed_map.to_quotient_map IsClosedMap.to_quotientMap

end IsClosedMap

theorem Inducing.isClosedMap [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : Inducing f)
    (h : IsClosed (range f)) : IsClosedMap f := by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h
#align inducing.is_closed_map Inducing.isClosedMap

theorem isClosedMap_iff_closure_image [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
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
theorem isClosedMap_iff_clusterPt [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsClosedMap f ↔ ∀ s y, MapClusterPt y (𝓟 s) f → ∃ x, f x = y ∧ ClusterPt x (𝓟 s) := by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

theorem IsClosedMap.closure_image_eq_of_continuous [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set α) :
    closure (f '' s) = f '' closure s :=
  subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

theorem IsClosedMap.lift'_closure_map_eq [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter α) :
    (map f F).lift' closure = map f (F.lift' closure) := by
  rw [map_lift'_eq2 (monotone_closure β), map_lift'_eq (monotone_closure α)]
  congr
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

theorem IsClosedMap.mapClusterPt_iff_lift'_closure [TopologicalSpace α] [TopologicalSpace β]
    {F : Filter α} {f : α → β} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : β} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt, clusterPt_iff_lift'_closure', f_closed.lift'_closure_map_eq f_cont,
      ← comap_principal, ← map_neBot_iff f, Filter.push_pull, principal_singleton]

section OpenEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- An open embedding is an embedding with open image. -/
@[mk_iff]
structure OpenEmbedding (f : α → β) extends Embedding f : Prop where
  /-- The range of an open embedding is an open set. -/
  open_range : IsOpen <| range f
#align open_embedding OpenEmbedding
#align open_embedding_iff openEmbedding_iff

theorem OpenEmbedding.isOpenMap {f : α → β} (hf : OpenEmbedding f) : IsOpenMap f :=
  hf.toEmbedding.toInducing.isOpenMap hf.open_range
#align open_embedding.is_open_map OpenEmbedding.isOpenMap

theorem OpenEmbedding.map_nhds_eq {f : α → β} (hf : OpenEmbedding f) (a : α) :
    map f (𝓝 a) = 𝓝 (f a) :=
  hf.toEmbedding.map_nhds_of_mem _ <| hf.open_range.mem_nhds <| mem_range_self _
#align open_embedding.map_nhds_eq OpenEmbedding.map_nhds_eq

theorem OpenEmbedding.open_iff_image_open {f : α → β} (hf : OpenEmbedding f) {s : Set α} :
    IsOpen s ↔ IsOpen (f '' s) :=
  ⟨hf.isOpenMap s, fun h => by
    convert ← h.preimage hf.toEmbedding.continuous
    apply preimage_image_eq _ hf.inj⟩
#align open_embedding.open_iff_image_open OpenEmbedding.open_iff_image_open

theorem OpenEmbedding.tendsto_nhds_iff {ι : Type*} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β}
    (hg : OpenEmbedding g) : Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.toEmbedding.tendsto_nhds_iff
#align open_embedding.tendsto_nhds_iff OpenEmbedding.tendsto_nhds_iff

theorem OpenEmbedding.tendsto_nhds_iff' {f : α → β} (hf : OpenEmbedding f) {g : β → γ}
    {l : Filter γ} {a : α} : Tendsto (g ∘ f) (𝓝 a) l ↔ Tendsto g (𝓝 (f a)) l := by
  rw [Tendsto, ← map_map, hf.map_nhds_eq]; rfl

theorem OpenEmbedding.continuousAt_iff {f : α → β} (hf : OpenEmbedding f) {g : β → γ} {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'
#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iff

theorem OpenEmbedding.continuous {f : α → β} (hf : OpenEmbedding f) : Continuous f :=
  hf.toEmbedding.continuous
#align open_embedding.continuous OpenEmbedding.continuous

theorem OpenEmbedding.open_iff_preimage_open {f : α → β} (hf : OpenEmbedding f) {s : Set β}
    (hs : s ⊆ range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.open_iff_image_open, image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]
#align open_embedding.open_iff_preimage_open OpenEmbedding.open_iff_preimage_open

theorem openEmbedding_of_embedding_open {f : α → β} (h₁ : Embedding f) (h₂ : IsOpenMap f) :
    OpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩
#align open_embedding_of_embedding_open openEmbedding_of_embedding_open

/-- A surjective embedding is an `OpenEmbedding`. -/
theorem _root_.Embedding.toOpenEmbedding_of_surjective {f : α → β}
    (hf : Embedding f) (hsurj: f.Surjective) : OpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

theorem openEmbedding_iff_embedding_open {f : α → β} :
    OpenEmbedding f ↔ Embedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => openEmbedding_of_embedding_open h.1 h.2⟩
#align open_embedding_iff_embedding_open openEmbedding_iff_embedding_open

theorem openEmbedding_of_continuous_injective_open {f : α → β} (h₁ : Continuous f)
    (h₂ : Injective f) (h₃ : IsOpenMap f) : OpenEmbedding f := by
  simp only [openEmbedding_iff_embedding_open, embedding_iff, inducing_iff_nhds, *, and_true_iff]
  exact fun a =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 a) _ h₂ ▸ comap_mono (h₃.nhds_le _))
#align open_embedding_of_continuous_injective_open openEmbedding_of_continuous_injective_open

theorem openEmbedding_iff_continuous_injective_open {f : α → β} :
    OpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.inj, h.isOpenMap⟩, fun h =>
    openEmbedding_of_continuous_injective_open h.1 h.2.1 h.2.2⟩
#align open_embedding_iff_continuous_injective_open openEmbedding_iff_continuous_injective_open

theorem openEmbedding_id : OpenEmbedding (@id α) :=
  ⟨embedding_id, IsOpenMap.id.isOpen_range⟩
#align open_embedding_id openEmbedding_id

protected theorem OpenEmbedding.comp {g : β → γ} {f : α → β} (hg : OpenEmbedding g)
    (hf : OpenEmbedding f) : OpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩
#align open_embedding.comp OpenEmbedding.comp

theorem OpenEmbedding.isOpenMap_iff {g : β → γ} {f : α → β} (hg : OpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, Filter.map_le_map_iff hg.inj]
#align open_embedding.is_open_map_iff OpenEmbedding.isOpenMap_iff

theorem OpenEmbedding.of_comp_iff (f : α → β) {g : β → γ} (hg : OpenEmbedding g) :
    OpenEmbedding (g ∘ f) ↔ OpenEmbedding f := by
  simp only [openEmbedding_iff_continuous_injective_open, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.inj.of_comp_iff]
#align open_embedding.of_comp_iff OpenEmbedding.of_comp_iff

theorem OpenEmbedding.of_comp (f : α → β) {g : β → γ} (hg : OpenEmbedding g)
    (h : OpenEmbedding (g ∘ f)) : OpenEmbedding f :=
  (OpenEmbedding.of_comp_iff f hg).1 h
#align open_embedding.of_comp OpenEmbedding.of_comp

end OpenEmbedding

section ClosedEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A closed embedding is an embedding with closed image. -/
@[mk_iff]
structure ClosedEmbedding (f : α → β) extends Embedding f : Prop where
  /-- The range of a closed embedding is a closed set. -/
  closed_range : IsClosed <| range f
#align closed_embedding ClosedEmbedding
#align closed_embedding_iff closedEmbedding_iff

variable {f : α → β}

theorem ClosedEmbedding.tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : Filter ι} {b : α}
    (hf : ClosedEmbedding f) : Tendsto g a (𝓝 b) ↔ Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.toEmbedding.tendsto_nhds_iff
#align closed_embedding.tendsto_nhds_iff ClosedEmbedding.tendsto_nhds_iff

theorem ClosedEmbedding.continuous (hf : ClosedEmbedding f) : Continuous f :=
  hf.toEmbedding.continuous
#align closed_embedding.continuous ClosedEmbedding.continuous

theorem ClosedEmbedding.isClosedMap (hf : ClosedEmbedding f) : IsClosedMap f :=
  hf.toEmbedding.toInducing.isClosedMap hf.closed_range
#align closed_embedding.is_closed_map ClosedEmbedding.isClosedMap

theorem ClosedEmbedding.closed_iff_image_closed (hf : ClosedEmbedding f) {s : Set α} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.inj]
    exact h.preimage hf.continuous⟩
#align closed_embedding.closed_iff_image_closed ClosedEmbedding.closed_iff_image_closed

theorem ClosedEmbedding.closed_iff_preimage_closed (hf : ClosedEmbedding f) {s : Set β}
    (hs : s ⊆ range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.closed_iff_image_closed, image_preimage_eq_of_subset hs]
#align closed_embedding.closed_iff_preimage_closed ClosedEmbedding.closed_iff_preimage_closed

theorem closedEmbedding_of_embedding_closed (h₁ : Embedding f) (h₂ : IsClosedMap f) :
    ClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩
#align closed_embedding_of_embedding_closed closedEmbedding_of_embedding_closed

theorem closedEmbedding_of_continuous_injective_closed (h₁ : Continuous f) (h₂ : Injective f)
    (h₃ : IsClosedMap f) : ClosedEmbedding f := by
  refine closedEmbedding_of_embedding_closed ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl, preimage_image_eq _ h₂, compl_compl]
#align closed_embedding_of_continuous_injective_closed closedEmbedding_of_continuous_injective_closed

theorem closedEmbedding_id : ClosedEmbedding (@id α) :=
  ⟨embedding_id, IsClosedMap.id.closed_range⟩
#align closed_embedding_id closedEmbedding_id

theorem ClosedEmbedding.comp {g : β → γ} {f : α → β} (hg : ClosedEmbedding g)
    (hf : ClosedEmbedding f) : ClosedEmbedding (g ∘ f) :=
  ⟨hg.toEmbedding.comp hf.toEmbedding, (hg.isClosedMap.comp hf.isClosedMap).closed_range⟩
#align closed_embedding.comp ClosedEmbedding.comp

theorem ClosedEmbedding.closure_image_eq {f : α → β} (hf : ClosedEmbedding f) (s : Set α) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s
#align closed_embedding.closure_image_eq ClosedEmbedding.closure_image_eq

end ClosedEmbedding
