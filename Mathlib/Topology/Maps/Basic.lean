/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Topology.NhdsSet

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `IsInducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `IsCoinducing f` means the topology on `Y` is the one coinduced via `f` from the topology on `X`.
* `IsEmbedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `IsOpenEmbedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `IsClosedEmbedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `IsQuotientMap f` is the dual condition to `IsEmbedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

public section


open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X → Y} {g : Y → Z}

namespace Topology
section IsInducing

variable [TopologicalSpace Y]

protected lemma IsInducing.induced (f : X → Y) : @IsInducing X Y (induced f ‹_›) _ f :=
  @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

variable [TopologicalSpace X]

@[fun_prop]
protected lemma IsInducing.id : IsInducing (@id X) := ⟨induced_id.symm⟩

variable [TopologicalSpace Z]

@[fun_prop]
protected lemma IsInducing.comp (hg : IsInducing g) (hf : IsInducing f) :
    IsInducing (g ∘ f) :=
  ⟨by rw [hf.eq_induced, hg.eq_induced, induced_compose]⟩

lemma IsInducing.of_comp_iff (hg : IsInducing g) : IsInducing (g ∘ f) ↔ IsInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [isInducing_iff, hg.eq_induced, induced_compose, h.eq_induced]

lemma IsInducing.of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsInducing (g ∘ f)) :
    IsInducing f :=
  ⟨le_antisymm hf.le_induced (by grw [hgf.eq_induced, ← induced_compose, ← hg.le_induced])⟩

lemma isInducing_iff_nhds : IsInducing f ↔ ∀ x, 𝓝 x = comap f (𝓝 (f x)) :=
  (isInducing_iff _).trans (induced_iff_nhds_eq f)

namespace IsInducing

lemma nhds_eq_comap (hf : IsInducing f) : ∀ x : X, 𝓝 x = comap f (𝓝 <| f x) :=
  isInducing_iff_nhds.1 hf

lemma basis_nhds {p : ι → Prop} {s : ι → Set Y} (hf : IsInducing f) {x : X}
    (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s) :=
  hf.nhds_eq_comap x ▸ h_basis.comap f

lemma nhdsSet_eq_comap (hf : IsInducing f) (s : Set X) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]

lemma map_nhds_eq (hf : IsInducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.eq_induced ▸ map_nhds_induced_eq x

lemma map_nhds_of_mem (hf : IsInducing f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) := hf.eq_induced ▸ map_nhds_induced_of_mem h

lemma mapClusterPt_iff (hf : IsInducing f) {x : X} {l : Filter X} :
    MapClusterPt (f x) l f ↔ ClusterPt x l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull', ← hf.nhds_eq_comap, map_neBot_iff]

lemma image_mem_nhdsWithin (hf : IsInducing f) {x : X} {s : Set X} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝[range f] f x :=
  hf.map_nhds_eq x ▸ image_mem_map hs

lemma tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : IsInducing g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]

lemma continuousAt_iff (hg : IsInducing g) {x : X} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff

lemma continuous_iff (hg : IsInducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]

lemma continuousAt_iff' (hf : IsInducing f) {x : X} (h : range f ∈ 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

@[fun_prop]
protected lemma continuous (hf : IsInducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

lemma closure_eq_preimage_closure_image (hf : IsInducing f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.eq_induced]

theorem isClosed_iff (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isClosed_induced_iff]

theorem isClosed_iff' (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s := by rw [hf.eq_induced, isClosed_induced_iff']

theorem isClosed_preimage (h : IsInducing f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (isClosed_iff h).mpr ⟨s, hs, rfl⟩

theorem isOpen_iff (hf : IsInducing f) {s : Set X} :
    IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isOpen_induced_iff]

theorem setOf_isOpen (hf : IsInducing f) :
    {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ ↦ hf.isOpen_iff

theorem dense_iff (hf : IsInducing f) {s : Set X} :
    Dense s ↔ ∀ x, f x ∈ closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]

theorem of_subsingleton [Subsingleton X] (f : X → Y) : IsInducing f :=
  ⟨Subsingleton.elim _ _⟩

theorem indiscreteTopology [IndiscreteTopology Y] {f : X → Y} (hf : IsInducing f) :
    IndiscreteTopology X where
  eq_top := by
    cases IndiscreteTopology.eq_top Y
    letI : TopologicalSpace Y := ⊤
    rw [hf.eq_induced, induced_top]

theorem nontrivialTopology [NontrivialTopology X] {f : X → Y} (hf : IsInducing f) :
    NontrivialTopology Y :=
  not_imp_not.1
    (by simpa using (fun _ : IndiscreteTopology Y => hf.indiscreteTopology)) ‹NontrivialTopology X›

end IsInducing.IsInducing

namespace IsEmbedding

lemma induced [t : TopologicalSpace Y] (hf : Injective f) :
    @IsEmbedding X Y (t.induced f) t f :=
  @IsEmbedding.mk X Y (t.induced f) t _ (.induced f) hf

alias _root_.Function.Injective.isEmbedding_induced := IsEmbedding.induced

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[fun_prop]
lemma isInducing (hf : IsEmbedding f) : IsInducing f := hf.toIsInducing

lemma mk' (f : X → Y) (inj : Injective f) (induced : ∀ x, comap f (𝓝 (f x)) = 𝓝 x) :
    IsEmbedding f :=
  ⟨isInducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

@[fun_prop]
protected lemma id : IsEmbedding (@id X) := ⟨.id, fun _ _ h => h⟩

@[fun_prop]
protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
  { hg.isInducing.comp hf.isInducing with injective := fun _ _ h => hf.injective <| hg.injective h }

lemma of_comp_iff (hg : IsEmbedding g) : IsEmbedding (g ∘ f) ↔ IsEmbedding f := by
  simp_rw [isEmbedding_iff, hg.isInducing.of_comp_iff, hg.injective.of_comp_iff f]

protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsEmbedding (g ∘ f)) :
    IsEmbedding f where
  toIsInducing := hgf.isInducing.of_comp hf hg
  injective := hgf.injective.of_comp

lemma of_leftInverse {f : X → Y} {g : Y → X} (h : LeftInverse f g) (hf : Continuous f)
    (hg : Continuous g) : IsEmbedding g := .of_comp hg hf <| h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse

lemma map_nhds_eq (hf : IsEmbedding f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.1.map_nhds_eq x

lemma map_nhds_of_mem (hf : IsEmbedding f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.1.map_nhds_of_mem x h

lemma tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : IsEmbedding g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := hg.isInducing.tendsto_nhds_iff

lemma continuous_iff (hg : IsEmbedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  hg.isInducing.continuous_iff

@[fun_prop]
lemma continuous (hf : IsEmbedding f) : Continuous f := hf.isInducing.continuous

lemma closure_eq_preimage_closure_image (hf : IsEmbedding f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) :=
  hf.1.closure_eq_preimage_closure_image s

/-- The topology induced under an inclusion `f : X → Y` from a discrete topological space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`. -/
lemma discreteTopology [DiscreteTopology Y] (hf : IsEmbedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.injective

lemma of_subsingleton [Subsingleton X] (f : X → Y) : IsEmbedding f :=
  ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

end IsEmbedding

section IsCoinducing

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma isCoinducing_iff : IsCoinducing f ↔ ∀ s : Set Y, IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  (isCoinducing_iff' _).trans <| eq_comm.trans TopologicalSpace.ext_iff

lemma isCoinducing_iff_isClosed :
    IsCoinducing f ↔ ∀ s : Set Y, IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  isCoinducing_iff.trans <| compl_surjective.forall.trans <| by simp

namespace IsCoinducing

protected lemma isOpen_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  isCoinducing_iff.mp hf _

protected lemma isClosed_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  isCoinducing_iff_isClosed.mp hf _

alias ⟨_, of_isOpen_preimage_iff_isOpen⟩ := isCoinducing_iff

alias ⟨_, of_isClosed_preimage_iff_isClosed⟩ := isCoinducing_iff_isClosed

protected lemma continuous (hf : IsCoinducing f) : Continuous f where
  isOpen_preimage s hs := by rwa [hf.isOpen_preimage]

variable (X) in
@[fun_prop]
protected lemma id : IsCoinducing (id (α := X)) where
  eq_coinduced := coinduced_id.symm

@[fun_prop]
protected lemma comp (hg : IsCoinducing g) (hf : IsCoinducing f) : IsCoinducing (g.comp f) where
  eq_coinduced := by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]

protected lemma of_comp_iff (hf : IsCoinducing f) :
    IsCoinducing (g ∘ f) ↔ IsCoinducing g := by
  refine ⟨fun hgf ↦ .of_isOpen_preimage_iff_isOpen fun s ↦ ?_, fun hg ↦ hg.comp hf⟩
  rw [← hgf.isOpen_preimage, Set.preimage_comp, hf.isOpen_preimage]

protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsCoinducing (g ∘ f)) :
    IsCoinducing g :=
  ⟨le_antisymm (by grw [hgf.eq_coinduced, ← coinduced_compose, hf.coinduced_le]) hg.coinduced_le⟩

lemma isOpenMap_of_injective (hf : IsCoinducing f) (hf' : Injective f) : IsOpenMap f := by
  intro s hs
  rwa [← hf.isOpen_preimage, preimage_image_eq _ hf']

end IsCoinducing

end IsCoinducing

section IsQuotientMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem isQuotientMap_iff_isClosed :
    IsQuotientMap f ↔ Surjective f ∧ ∀ s : Set Y, IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  simp_rw [isQuotientMap_iff, isCoinducing_iff_isClosed, and_comm, iff_comm]

namespace IsQuotientMap

@[fun_prop]
protected theorem id : IsQuotientMap (@id X) :=
  ⟨.id _, fun x => ⟨x, rfl⟩⟩

@[fun_prop]
protected theorem comp (hg : IsQuotientMap g) (hf : IsQuotientMap f) : IsQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, hg.surjective.comp hf.surjective, ⟩

protected theorem of_comp (hf : Continuous f) (hg : Continuous g)
    (hgf : IsQuotientMap (g ∘ f)) : IsQuotientMap g :=
  ⟨.of_comp hf hg hgf.1, hgf.2.of_comp⟩

theorem of_comp_of_isCoinducing (hgf : IsQuotientMap (g ∘ f)) (hf : IsCoinducing f) :
    IsQuotientMap g :=
  ⟨hf.of_comp_iff.mp hgf.1, hgf.2.of_comp⟩

@[deprecated (since := "2026-03-21")]
alias of_comp_of_eq_coinduced := of_comp_of_isCoinducing

theorem of_comp_isQuotientMap (hf : IsQuotientMap f) (hgf : IsQuotientMap (g ∘ f)) :
    IsQuotientMap g := of_comp_of_isCoinducing hgf hf.isCoinducing

theorem of_inverse {g : Y → X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
    IsQuotientMap g := .of_comp hf hg <| h.comp_eq_id.symm ▸ IsQuotientMap.id

protected theorem continuous_iff (hf : IsQuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.eq_coinduced, coinduced_compose]

@[fun_prop]
protected theorem continuous (hf : IsQuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

end IsQuotientMap

end Topology.IsQuotientMap

section OpenMap
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsOpenMap

protected theorem id : IsOpenMap (@id X) := fun s hs => by rwa [image_id]

protected theorem comp (hg : IsOpenMap g) (hf : IsOpenMap f) :
    IsOpenMap (g ∘ f) := fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)

theorem isOpen_range (hf : IsOpenMap f) : IsOpen (range f) := by
  rw [← image_univ]
  exact hf _ isOpen_univ

theorem image_mem_nhds (hf : IsOpenMap f) {x : X} {s : Set X} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_mono hts)

theorem range_mem_nhds (hf : IsOpenMap f) (x : X) : range f ∈ 𝓝 (f x) :=
  hf.isOpen_range.mem_nhds <| mem_range_self _

theorem mapsTo_interior (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
  mapsTo_iff_image_subset.2 <|
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)

theorem image_interior_subset (hf : IsOpenMap f) (s : Set X) :
    f '' interior s ⊆ interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset

theorem nhds_le (hf : IsOpenMap f) (x : X) : 𝓝 (f x) ≤ map f (𝓝 x) :=
  le_map fun _ => hf.image_mem_nhds

theorem map_nhds_eq (hf : IsOpenMap f) {x : X} (hf' : ContinuousAt f x) : map f (𝓝 x) = 𝓝 (f x) :=
  le_antisymm hf' (hf.nhds_le x)

theorem map_nhdsSet_eq (hf : IsOpenMap f) (hf' : Continuous f) (s : Set X) :
    map f (𝓝ˢ s) = 𝓝ˢ (f '' s) := by
  rw [← biUnion_of_singleton s]
  simp_rw [image_iUnion, nhdsSet_iUnion, map_iSup, image_singleton, nhdsSet_singleton,
    hf.map_nhds_eq hf'.continuousAt]

theorem of_nhds_le (hf : ∀ x, 𝓝 (f x) ≤ map f (𝓝 x)) : IsOpenMap f := fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)

theorem of_sections
    (h : ∀ x, ∃ g : Y → X, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) : IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ ≤ map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]

theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsOpenMap f :=
  of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩

/-- A continuous surjective open map is a quotient map. -/
theorem isQuotientMap (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f) :
    IsQuotientMap f := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, surj⟩
  exact ⟨fun h => surj.image_preimage s ▸ open_map _ h, fun h => h.preimage cont⟩

theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set Y} :
    interior (f ⁻¹' s) ⊆ f ⁻¹' interior s :=
  hf.mapsTo_interior (mapsTo_preimage _ _)

theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
    (s : Set Y) : f ⁻¹' interior s = interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)

theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' closure s ⊆ closure (f ⁻¹' s) := by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]

theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' closure s = closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

lemma preimage_closure_image_eq_id (h₁ : IsOpenMap f) (h₂ : Function.Injective f)
    (h₃ : Continuous f) (s : Set X) (hs' : IsClosed s) : f ⁻¹' closure (f '' s) = s := by
  rw [h₁.preimage_closure_eq_closure_preimage h₃, Set.preimage_image_eq _ h₂, hs'.closure_eq]

theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' frontier s ⊆ frontier (f ⁻¹' s) := by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage

theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' frontier s = frontier (f ⁻¹' s) := by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]

theorem of_isEmpty [h : IsEmpty X] (f : X → Y) : IsOpenMap f := of_nhds_le h.elim

theorem clusterPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : ClusterPt (f x) l) :
    ClusterPt x (comap f l) := by
  rw [ClusterPt, ← map_neBot_iff, Filter.push_pull]
  exact h.neBot.mono <| inf_le_inf_right _ <| hf.nhds_le _

theorem accPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : AccPt (f x) l) :
    AccPt x (comap f l) := by
  rw [accPt_iff_clusterPt] at h ⊢
  apply (hf.clusterPt_comap h).mono
  rw [comap_inf, comap_principal, preimage_compl]
  exact inf_le_inf_right (comap f l) (by simp)

theorem clusterPt_comap_iff (hf : IsOpenMap f) (hfc : Continuous f) {x : X} {l : Filter Y} :
    ClusterPt x (comap f l) ↔ ClusterPt (f x) l :=
  ⟨fun h => h.map hfc.continuousAt tendsto_comap, hf.clusterPt_comap⟩

end IsOpenMap

/-- A map is open if and only if the `Set.kernImage` of every *closed* set is closed.

One way to understand this result is that `f : X → Y` is open if and only if its fibers vary in a
**lower hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y` such that
`(f ⁻¹' {y} ∩ U).Nonempty` is open in `Y`. See `isOpenMap_iff_lowerHemicontinuous`. -/
lemma isOpenMap_iff_kernImage :
    IsOpenMap f ↔ ∀ {u : Set X}, IsClosed u → IsClosed (kernImage f u) := by
  rw [IsOpenMap, compl_surjective.forall]
  simp [kernImage_eq_compl]

theorem isOpenMap_iff_nhds_le : IsOpenMap f ↔ ∀ x : X, 𝓝 (f x) ≤ (𝓝 x).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

theorem isOpenMap_iff_clusterPt_comap :
    IsOpenMap f ↔ ∀ x l, ClusterPt (f x) l → ClusterPt x (comap f l) := by
  refine ⟨fun hf _ _ ↦ hf.clusterPt_comap, fun h ↦ ?_⟩
  simp only [isOpenMap_iff_nhds_le, le_map_iff]
  intro x s hs
  contrapose hs
  rw [← mem_interior_iff_mem_nhds, mem_interior_iff_not_clusterPt_compl, not_not] at hs ⊢
  exact (h _ _ hs).mono <| by simp [subset_preimage_image]

theorem isOpenMap_iff_image_interior : IsOpenMap f ↔ ∀ s, f '' interior s ⊆ interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_isOpen.mp <| by simpa only [hu.interior_eq] using hs u⟩

/-- A map is open if and only if the `Set.kernImage` of every *closed* set is closed. -/
lemma isOpenMap_iff_closure_kernImage :
    IsOpenMap f ↔ ∀ {s : Set X}, closure (kernImage f s) ⊆ kernImage f (closure s) := by
  rw [isOpenMap_iff_image_interior, compl_surjective.forall]
  simp [kernImage_eq_compl]

/-- An inducing map with an open range is an open map. -/
protected lemma Topology.IsInducing.isOpenMap (hi : IsInducing f) (ho : IsOpen (range f)) :
    IsOpenMap f :=
  IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge

/-- Preimage of a dense set under an open map is dense. -/
protected theorem Dense.preimage {s : Set Y} (hs : Dense s) (hf : IsOpenMap f) :
    Dense (f ⁻¹' s) := fun x ↦
  hf.preimage_closure_subset_closure_preimage <| hs (f x)

end OpenMap

section IsClosedMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedMap
open Function

protected theorem id : IsClosedMap (@id X) := fun s hs => by rwa [image_id]

protected theorem comp (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)

protected theorem of_comp_surjective (hf : Surjective f) (hf' : Continuous f)
    (hfg : IsClosedMap (g ∘ f)) : IsClosedMap g := by
  intro K hK
  rw [← image_preimage_eq K hf, ← image_comp]
  exact hfg _ (hK.preimage hf')

theorem closure_image_subset (hf : IsClosedMap f) (s : Set X) :
    closure (f '' s) ⊆ f '' closure s :=
  closure_minimal (image_mono subset_closure) (hf _ isClosed_closure)

theorem of_inverse {f' : Y → X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsClosedMap f := fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h

theorem of_nonempty (h : ∀ s, IsClosed s → s.Nonempty → IsClosed (f '' s)) :
    IsClosedMap f := by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s

theorem isClosed_range (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ isClosed_univ


theorem isQuotientMap (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : IsQuotientMap f :=
  isQuotientMap_iff_isClosed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

end IsClosedMap

/-- A map is closed if and only if the `Set.kernImage` of every *open* set is open.

One way to understand this result is that `f : X → Y` is closed if and only if its fibers vary in an
**upper hemicontinuous** way: for any open subset `U ⊆ X`, the set of all `y ∈ Y` such that
`f ⁻¹' {y} ⊆ U` is open in `Y`. See `isClosedMap_iff_upperHemicontinuous`. -/
lemma isClosedMap_iff_kernImage :
    IsClosedMap f ↔ ∀ {u : Set X}, IsOpen u → IsOpen (kernImage f u) := by
  rw [IsClosedMap, compl_surjective.forall]
  simp [kernImage_eq_compl]

lemma Topology.IsInducing.isClosedMap (hf : IsInducing f) (h : IsClosed (range f)) :
    IsClosedMap f := by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h

theorem isClosedMap_iff_closure_image :
    IsClosedMap f ↔ ∀ s, closure (f '' s) ⊆ f '' closure s :=
  ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
    isClosed_of_closure_subset <|
      calc
        closure (f '' c) ⊆ f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩

theorem isClosedMap_iff_kernImage_interior :
    IsClosedMap f ↔ ∀ {s : Set X}, kernImage f (interior s) ⊆ interior (kernImage f s) := by
  rw [isClosedMap_iff_closure_image, compl_surjective.forall]
  simp [kernImage_eq_compl]

/-- A map `f : X → Y` is closed if and only if for all sets `s`, any cluster point of `f '' s` is
the image by `f` of some cluster point of `s`.
If you require this for all filters instead of just principal filters, and also that `f` is
continuous, you get the notion of **proper map**. See `isProperMap_iff_clusterPt`. -/
theorem isClosedMap_iff_clusterPt :
    IsClosedMap f ↔ ∀ s y, MapClusterPt y (𝓟 s) f → ∃ x, f x = y ∧ ClusterPt x (𝓟 s) := by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

theorem isClosedMap_iff_comap_nhdsSet_le :
    IsClosedMap f ↔ ∀ {s : Set Y}, comap f (𝓝ˢ s) ≤ 𝓝ˢ (f ⁻¹' s) := by
  simp_rw [Filter.le_def, mem_comap'', ← subset_interior_iff_mem_nhdsSet,
    ← subset_kernImage_iff, isClosedMap_iff_kernImage_interior]
  exact ⟨fun H s t hst ↦ hst.trans H, fun H s ↦ H _ subset_rfl⟩

alias ⟨IsClosedMap.comap_nhdsSet_le, _⟩ := isClosedMap_iff_comap_nhdsSet_le

theorem isClosedMap_iff_comap_nhds_le :
    IsClosedMap f ↔ ∀ {y : Y}, comap f (𝓝 y) ≤ 𝓝ˢ (f ⁻¹' {y}) := by
  rw [isClosedMap_iff_comap_nhdsSet_le]
  constructor
  · exact fun H y ↦ nhdsSet_singleton (x := y) ▸ H
  · intro H s
    rw [← Set.biUnion_of_singleton s]
    simp_rw [preimage_iUnion, nhdsSet_iUnion, comap_iSup, nhdsSet_singleton]
    exact iSup₂_mono fun _ _ ↦ H

alias ⟨IsClosedMap.comap_nhds_le, _⟩ := isClosedMap_iff_comap_nhds_le

theorem IsClosedMap.comap_nhds_eq (hf : IsClosedMap f) (hf' : Continuous f) (y : Y) :
    comap f (𝓝 y) = 𝓝ˢ (f ⁻¹' {y}) :=
  le_antisymm (isClosedMap_iff_comap_nhds_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhds`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx ↦ hx ▸ (hf'.tendsto x).le_comap)

theorem IsClosedMap.comap_nhdsSet_eq (hf : IsClosedMap f) (hf' : Continuous f) (s : Set Y) :
    comap f (𝓝ˢ s) = 𝓝ˢ (f ⁻¹' s) :=
  le_antisymm (isClosedMap_iff_comap_nhdsSet_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhdsSet`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx ↦ (hf'.tendsto x).le_comap.trans (comap_mono (nhds_le_nhdsSet hx)))

/-- Assume `f` is a closed map. If some property `p` holds around every point in the fiber of `f`
at `y₀`, then for any `y` close enough to `y₀` we have that `p` holds on the fiber at `y`. -/
theorem IsClosedMap.eventually_nhds_fiber (hf : IsClosedMap f) {p : X → Prop} (y₀ : Y)
    (H : ∀ x₀ ∈ f ⁻¹' {y₀}, ∀ᶠ x in 𝓝 x₀, p x) :
    ∀ᶠ y in 𝓝 y₀, ∀ x ∈ f ⁻¹' {y}, p x := by
  rw [← eventually_nhdsSet_iff_forall] at H
  replace H := H.filter_mono hf.comap_nhds_le
  rwa [eventually_comap] at H

/-- Assume `f` is a closed map. If there are points `y` arbitrarily close to `y₀` such that `p`
holds for at least some `x ∈ f ⁻¹' {y}`, then one can find `x₀ ∈ f ⁻¹' {y₀}` such that there
are points `x` arbitrarily close to `x₀` which satisfy `p`. -/
theorem IsClosedMap.frequently_nhds_fiber (hf : IsClosedMap f) {p : X → Prop} (y₀ : Y)
    (H : ∃ᶠ y in 𝓝 y₀, ∃ x ∈ f ⁻¹' {y}, p x) :
    ∃ x₀ ∈ f ⁻¹' {y₀}, ∃ᶠ x in 𝓝 x₀, p x := by
  /-
  Note: this result could also be seen as a reformulation of `isClosedMap_iff_clusterPt`.
  One would then be able to deduce the `eventually` statement,
  and then go back to `isClosedMap_iff_comap_nhdsSet_le`.
  Ultimately, this makes no difference.
  -/
  contrapose! H
  exact hf.eventually_nhds_fiber y₀ H

theorem IsClosedMap.closure_image_eq_of_continuous
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

theorem IsClosedMap.lift'_closure_map_eq
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter X) :
    (map f F).lift' closure = map f (F.lift' closure) := by
  rw [map_lift'_eq2 (monotone_closure Y), map_lift'_eq (monotone_closure X)]
  congr 1
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

theorem IsClosedMap.mapClusterPt_iff_lift'_closure
    {F : Filter X} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : Y} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt, clusterPt_iff_lift'_closure', f_closed.lift'_closure_map_eq f_cont,
      ← comap_principal, ← map_neBot_iff f, Filter.push_pull, principal_singleton]

end IsClosedMap

namespace Topology
section IsOpenEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y]

@[fun_prop]
lemma IsOpenEmbedding.isEmbedding (hf : IsOpenEmbedding f) : IsEmbedding f := hf.toIsEmbedding

lemma IsOpenEmbedding.isInducing (hf : IsOpenEmbedding f) : IsInducing f :=
  hf.isEmbedding.isInducing

lemma IsOpenEmbedding.isOpenMap (hf : IsOpenEmbedding f) : IsOpenMap f :=
  hf.isEmbedding.isInducing.isOpenMap hf.isOpen_range

theorem IsOpenEmbedding.map_nhds_eq (hf : IsOpenEmbedding f) (x : X) :
    map f (𝓝 x) = 𝓝 (f x) :=
  hf.isEmbedding.map_nhds_of_mem _ <| hf.isOpen_range.mem_nhds <| mem_range_self _

lemma IsOpenEmbedding.isOpen_iff_image_isOpen (hf : IsOpenEmbedding f) {s : Set X} :
    IsOpen s ↔ IsOpen (f '' s) where
  mp := hf.isOpenMap s
  mpr h := by convert ← h.preimage hf.isEmbedding.continuous; apply preimage_image_eq _ hf.injective

theorem IsOpenEmbedding.tendsto_nhds_iff [TopologicalSpace Z] {f : ι → Y} {l : Filter ι} {y : Y}
    (hg : IsOpenEmbedding g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.isEmbedding.tendsto_nhds_iff

theorem IsOpenEmbedding.tendsto_nhds_iff' (hf : IsOpenEmbedding f) {l : Filter Z} {x : X} :
    Tendsto (g ∘ f) (𝓝 x) l ↔ Tendsto g (𝓝 (f x)) l := by
  rw [Tendsto, ← map_map, hf.map_nhds_eq]; rfl

theorem IsOpenEmbedding.continuousAt_iff [TopologicalSpace Z] (hf : IsOpenEmbedding f) {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'

@[fun_prop]
theorem IsOpenEmbedding.continuous (hf : IsOpenEmbedding f) : Continuous f :=
  hf.isEmbedding.continuous

lemma IsOpenEmbedding.isOpen_iff_preimage_isOpen (hf : IsOpenEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.isOpen_iff_image_isOpen, image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

@[fun_prop]
lemma IsOpenEmbedding.of_isEmbedding_isOpenMap (h₁ : IsEmbedding f) (h₂ : IsOpenMap f) :
    IsOpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩

/-- A surjective embedding is an `IsOpenEmbedding`. -/
lemma IsEmbedding.isOpenEmbedding_of_surjective (hf : IsEmbedding f) (hsurj : f.Surjective) :
    IsOpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

alias IsOpenEmbedding.of_isEmbedding := IsEmbedding.isOpenEmbedding_of_surjective

lemma isOpenEmbedding_iff_isEmbedding_isOpenMap : IsOpenEmbedding f ↔ IsEmbedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩

theorem IsOpenEmbedding.of_continuous_injective_isOpenMap
    (h₁ : Continuous f) (h₂ : Injective f) (h₃ : IsOpenMap f) : IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, isInducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))

lemma isOpenEmbedding_iff_continuous_injective_isOpenMap :
    IsOpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.injective, h.isOpenMap⟩, fun h =>
    .of_continuous_injective_isOpenMap h.1 h.2.1 h.2.2⟩

namespace IsOpenEmbedding
variable [TopologicalSpace Z]

@[fun_prop]
protected lemma id : IsOpenEmbedding (@id X) := ⟨.id, IsOpenMap.id.isOpen_range⟩

@[fun_prop]
protected lemma comp (hg : IsOpenEmbedding g)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩

theorem isOpenMap_iff (hg : IsOpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, map_le_map_iff hg.injective]

theorem of_comp_iff (f : X → Y) (hg : IsOpenEmbedding g) :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_continuous_injective_isOpenMap, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.injective.of_comp_iff]

lemma of_comp (f : X → Y) (hg : IsOpenEmbedding g) (h : IsOpenEmbedding (g ∘ f)) :
    IsOpenEmbedding f := (IsOpenEmbedding.of_comp_iff f hg).1 h

theorem of_isEmpty [IsEmpty X] (f : X → Y) : IsOpenEmbedding f :=
  of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)

theorem image_mem_nhds {f : X → Y} (hf : IsOpenEmbedding f) {s : Set X} {x : X} :
    f '' s ∈ 𝓝 (f x) ↔ s ∈ 𝓝 x := by
  rw [← hf.map_nhds_eq, mem_map, preimage_image_eq _ hf.injective]

theorem accPt_comap_iff
    (hf : IsOpenEmbedding f) {x : X} {l : Filter Y} :
    AccPt x (comap f l) ↔ AccPt (f x) l := by
  rw [accPt_iff_clusterPt, accPt_iff_clusterPt, ← hf.injective.preimage_image {x}, image_singleton,
    ← preimage_compl, ← comap_principal, ← comap_inf,
    hf.isOpenMap.clusterPt_comap_iff hf.continuous]

end IsOpenEmbedding

end IsOpenEmbedding

section IsClosedEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedEmbedding

@[fun_prop]
lemma isEmbedding (hf : IsClosedEmbedding f) : IsEmbedding f := hf.toIsEmbedding
@[fun_prop]
lemma isInducing (hf : IsClosedEmbedding f) : IsInducing f := hf.isEmbedding.isInducing
@[fun_prop]
lemma continuous (hf : IsClosedEmbedding f) : Continuous f := hf.isEmbedding.continuous

lemma tendsto_nhds_iff {g : ι → X} {l : Filter ι} {x : X} (hf : IsClosedEmbedding f) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) := hf.isEmbedding.tendsto_nhds_iff

lemma isClosedMap (hf : IsClosedEmbedding f) : IsClosedMap f :=
  hf.isEmbedding.isInducing.isClosedMap hf.isClosed_range

lemma isClosed_iff_image_isClosed (hf : IsClosedEmbedding f) {s : Set X} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.injective]
    exact h.preimage hf.continuous⟩

lemma isClosed_iff_preimage_isClosed (hf : IsClosedEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.isClosed_iff_image_isClosed, image_preimage_eq_of_subset hs]

lemma of_isEmbedding_isClosedMap (h₁ : IsEmbedding f) (h₂ : IsClosedMap f) :
    IsClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩

lemma of_continuous_injective_isClosedMap (h₁ : Continuous f) (h₂ : Injective f)
    (h₃ : IsClosedMap f) : IsClosedEmbedding f := by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl, preimage_image_eq _ h₂, compl_compl]

lemma isClosedEmbedding_iff_continuous_injective_isClosedMap {f : X → Y} :
    IsClosedEmbedding f ↔ Continuous f ∧ Injective f ∧ IsClosedMap f where
  mp h := ⟨h.continuous, h.injective, h.isClosedMap⟩
  mpr h := .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2

@[fun_prop]
protected theorem id : IsClosedEmbedding (@id X) := ⟨.id, IsClosedMap.id.isClosed_range⟩

@[fun_prop]
theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (g ∘ f) :=
  ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩

lemma of_comp_iff (hg : IsClosedEmbedding g) : IsClosedEmbedding (g ∘ f) ↔ IsClosedEmbedding f := by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.isClosed_iff_image_isClosed]

protected lemma of_comp (hg : IsEmbedding g) (hgf : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f where
  __ := hg.of_comp_iff.mp hgf.isEmbedding
  isClosed_range := by
    convert hg.isClosed_preimage _ hgf.isClosed_range
    rw [range_comp, hg.injective.preimage_image]

theorem closure_image_eq (hf : IsClosedEmbedding f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

end Topology.IsClosedEmbedding.IsClosedEmbedding
