/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Order

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `Inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
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


open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X → Y} {g : Y → Z}

section Inducing

variable [TopologicalSpace Y]

theorem inducing_induced (f : X → Y) : @Inducing X Y (TopologicalSpace.induced f ‹_›) _ f :=
  @Inducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

variable [TopologicalSpace X]

theorem inducing_id : Inducing (@id X) :=
  ⟨induced_id.symm⟩

variable [TopologicalSpace Z]

protected theorem Inducing.comp (hg : Inducing g) (hf : Inducing f) :
    Inducing (g ∘ f) :=
  ⟨by rw [hf.induced, hg.induced, induced_compose]⟩

theorem Inducing.of_comp_iff (hg : Inducing g) :
    Inducing (g ∘ f) ↔ Inducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [inducing_iff, hg.induced, induced_compose, h.induced]

theorem inducing_of_inducing_compose
    (hf : Continuous f) (hg : Continuous g) (hgf : Inducing (g ∘ f)) : Inducing f :=
  ⟨le_antisymm (by rwa [← continuous_iff_le_induced])
      (by
        rw [hgf.induced, ← induced_compose]
        exact induced_mono hg.le_induced)⟩

theorem inducing_iff_nhds : Inducing f ↔ ∀ x, 𝓝 x = comap f (𝓝 (f x)) :=
  (inducing_iff _).trans (induced_iff_nhds_eq f)

namespace Inducing

theorem nhds_eq_comap (hf : Inducing f) : ∀ x : X, 𝓝 x = comap f (𝓝 <| f x) :=
  inducing_iff_nhds.1 hf

theorem basis_nhds {p : ι → Prop} {s : ι → Set Y} (hf : Inducing f) {x : X}
    (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s) :=
  hf.nhds_eq_comap x ▸ h_basis.comap f

theorem nhdsSet_eq_comap (hf : Inducing f) (s : Set X) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]

theorem map_nhds_eq (hf : Inducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.induced.symm ▸ map_nhds_induced_eq x

theorem map_nhds_of_mem (hf : Inducing f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.induced.symm ▸ map_nhds_induced_of_mem h

theorem mapClusterPt_iff (hf : Inducing f) {x : X} {l : Filter X} :
    MapClusterPt (f x) l f ↔ ClusterPt x l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull', ← hf.nhds_eq_comap, map_neBot_iff]

theorem image_mem_nhdsWithin (hf : Inducing f) {x : X} {s : Set X} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝[range f] f x :=
  hf.map_nhds_eq x ▸ image_mem_map hs

theorem tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : Inducing g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]

theorem continuousAt_iff (hg : Inducing g) {x : X} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff

theorem continuous_iff (hg : Inducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]

theorem continuousAt_iff' (hf : Inducing f) {x : X} (h : range f ∈ 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

protected theorem continuous (hf : Inducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

theorem closure_eq_preimage_closure_image (hf : Inducing f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.induced]

theorem isClosed_iff (hf : Inducing f) {s : Set X} :
    IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.induced, isClosed_induced_iff]

theorem isClosed_iff' (hf : Inducing f) {s : Set X} :
    IsClosed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s := by rw [hf.induced, isClosed_induced_iff']

theorem isClosed_preimage (h : Inducing f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (isClosed_iff h).mpr ⟨s, hs, rfl⟩

theorem isOpen_iff (hf : Inducing f) {s : Set X} :
    IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.induced, isOpen_induced_iff]

theorem setOf_isOpen (hf : Inducing f) :
    {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ ↦ hf.isOpen_iff

theorem dense_iff (hf : Inducing f) {s : Set X} :
    Dense s ↔ ∀ x, f x ∈ closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]

theorem of_subsingleton [Subsingleton X] (f : X → Y) : Inducing f :=
  ⟨Subsingleton.elim _ _⟩

end Inducing

end Inducing

namespace IsEmbedding

theorem Function.Injective.isEmbedding_induced [t : TopologicalSpace Y] (hf : Injective f) :
    @_root_.IsEmbedding X Y (t.induced f) t f :=
  @_root_.IsEmbedding.mk X Y (t.induced f) t _ (inducing_induced f) hf

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma mk' (f : X → Y) (inj : Injective f) (induced : ∀ x, comap f (𝓝 (f x)) = 𝓝 x) :
    IsEmbedding f :=
  ⟨inducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

protected lemma id : IsEmbedding (@id X) := ⟨inducing_id, fun _ _ h => h⟩

protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
  { hg.toInducing.comp hf.toInducing with inj := fun _ _ h => hf.inj <| hg.inj h }

lemma of_comp_iff (hg : IsEmbedding g) : IsEmbedding (g ∘ f) ↔ IsEmbedding f := by
  simp_rw [isEmbedding_iff, hg.toInducing.of_comp_iff, hg.inj.of_comp_iff f]

protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsEmbedding (g ∘ f)) :
    IsEmbedding f where
  toInducing := inducing_of_inducing_compose hf hg hgf.toInducing
  inj := hgf.inj.of_comp

lemma of_leftInverse {f : X → Y} {g : Y → X} (h : LeftInverse f g) (hf : Continuous f)
    (hg : Continuous g) : IsEmbedding g := .of_comp hg hf <| h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse

lemma map_nhds_eq (hf : IsEmbedding f) (x : X) :     (𝓝 x).map f = 𝓝[range f] f x :=
  hf.1.map_nhds_eq x

lemma map_nhds_of_mem (hf : IsEmbedding f) (x : X) (h : range f ∈ 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.1.map_nhds_of_mem x h

lemma tendsto_nhds_iff {f : ι → Y} {l : Filter ι} {y : Y} (hg : IsEmbedding g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := hg.toInducing.tendsto_nhds_iff

lemma continuous_iff (hg : IsEmbedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  hg.toInducing.continuous_iff

lemma continuous (hf : IsEmbedding f) : Continuous f := hf.toInducing.continuous

lemma closure_eq_preimage_closure_image (hf : IsEmbedding f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) :=
  hf.1.closure_eq_preimage_closure_image s

/-- The topology induced under an inclusion `f : X → Y` from a discrete topological space `Y`
is the discrete topology on `X`.

See also `DiscreteTopology.of_continuous_injective`. -/
lemma discreteTopology [DiscreteTopology Y] (hf : IsEmbedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.inj

lemma of_subsingleton [Subsingleton X] (f : X → Y) : IsEmbedding f :=
  ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

end IsEmbedding

section IsQuotientMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma isQuotientMap_iff : IsQuotientMap f ↔ Surjective f ∧ ∀ s, IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  (isQuotientMap_iff' _).trans <| and_congr Iff.rfl TopologicalSpace.ext_iff

@[deprecated (since := "2024-10-22")]
alias quotientMap_iff := isQuotientMap_iff

theorem isQuotientMap_iff_closed :
    IsQuotientMap f ↔ Surjective f ∧ ∀ s : Set Y, IsClosed s ↔ IsClosed (f ⁻¹' s) :=
  isQuotientMap_iff.trans <| Iff.rfl.and <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]

@[deprecated (since := "2024-10-22")]
alias quotientMap_iff_closed := isQuotientMap_iff_closed

namespace IsQuotientMap

protected theorem id : IsQuotientMap (@id X) :=
  ⟨fun x => ⟨x, rfl⟩, coinduced_id.symm⟩

protected theorem comp (hg : IsQuotientMap g) (hf : IsQuotientMap f) : IsQuotientMap (g ∘ f) :=
  ⟨hg.surjective.comp hf.surjective, by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]⟩

protected theorem of_comp (hf : Continuous f) (hg : Continuous g)
    (hgf : IsQuotientMap (g ∘ f)) : IsQuotientMap g :=
  ⟨hgf.1.of_comp,
    le_antisymm
      (by rw [hgf.eq_coinduced, ← coinduced_compose]; exact coinduced_mono hf.coinduced_le)
      hg.coinduced_le⟩

@[deprecated (since := "2024-10-22")]
alias of_quotientMap_compose := IsQuotientMap.of_comp

theorem of_inverse {g : Y → X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
    IsQuotientMap g := .of_comp hf hg <| h.comp_eq_id.symm ▸ IsQuotientMap.id

protected theorem continuous_iff (hf : IsQuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.eq_coinduced, coinduced_compose]

protected theorem continuous (hf : IsQuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

protected lemma isOpen_preimage (hf : IsQuotientMap f) {s : Set Y} : IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  ((isQuotientMap_iff.1 hf).2 s).symm

protected theorem isClosed_preimage (hf : IsQuotientMap f) {s : Set Y} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  ((isQuotientMap_iff_closed.1 hf).2 s).symm

end IsQuotientMap

end IsQuotientMap

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
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)

theorem range_mem_nhds (hf : IsOpenMap f) (x : X) : range f ∈ 𝓝 (f x) :=
  hf.isOpen_range.mem_nhds <| mem_range_self _

theorem mapsTo_interior (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
  mapsTo'.2 <|
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)

theorem image_interior_subset (hf : IsOpenMap f) (s : Set X) :
    f '' interior s ⊆ interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset

theorem nhds_le (hf : IsOpenMap f) (x : X) : 𝓝 (f x) ≤ (𝓝 x).map f :=
  le_map fun _ => hf.image_mem_nhds

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
    IsQuotientMap f :=
  isQuotientMap_iff.2
    ⟨surj, fun s => ⟨fun h => h.preimage cont, fun h => surj.image_preimage s ▸ open_map _ h⟩⟩

@[deprecated (since := "2024-10-22")]
alias to_quotientMap := isQuotientMap

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

end IsOpenMap

theorem isOpenMap_iff_nhds_le : IsOpenMap f ↔ ∀ x : X, 𝓝 (f x) ≤ (𝓝 x).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

theorem isOpenMap_iff_interior : IsOpenMap f ↔ ∀ s, f '' interior s ⊆ interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_isOpen.mp <|
      calc
        f '' u = f '' interior u := by rw [hu.interior_eq]
        _ ⊆ interior (f '' u) := hs u⟩

/-- An inducing map with an open range is an open map. -/
protected theorem Inducing.isOpenMap (hi : Inducing f) (ho : IsOpen (range f)) : IsOpenMap f :=
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

theorem closure_image_subset (hf : IsClosedMap f) (s : Set X) :
    closure (f '' s) ⊆ f '' closure s :=
  closure_minimal (image_subset _ subset_closure) (hf _ isClosed_closure)

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

@[deprecated (since := "2024-03-17")] alias closed_range := isClosed_range

theorem isQuotientMap (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : IsQuotientMap f :=
  isQuotientMap_iff_closed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

@[deprecated (since := "2024-10-22")]
alias to_quotientMap := isQuotientMap

end IsClosedMap

theorem Inducing.isClosedMap (hf : Inducing f) (h : IsClosed (range f)) : IsClosedMap f := by
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

section IsOpenEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y]

lemma IsOpenEmbedding.isEmbedding (hf : IsOpenEmbedding f) : IsEmbedding f := hf.toIsEmbedding
lemma IsOpenEmbedding.inducing (hf : IsOpenEmbedding f) : Inducing f :=
  hf.isEmbedding.toInducing

lemma IsOpenEmbedding.isOpenMap (hf : IsOpenEmbedding f) : IsOpenMap f :=
  hf.isEmbedding.toInducing.isOpenMap hf.isOpen_range

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.isOpenMap := IsOpenEmbedding.isOpenMap

theorem IsOpenEmbedding.map_nhds_eq (hf : IsOpenEmbedding f) (x : X) :
    map f (𝓝 x) = 𝓝 (f x) :=
  hf.isEmbedding.map_nhds_of_mem _ <| hf.isOpen_range.mem_nhds <| mem_range_self _

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.map_nhds_eq := IsOpenEmbedding.map_nhds_eq

theorem IsOpenEmbedding.open_iff_image_open (hf : IsOpenEmbedding f) {s : Set X} :
    IsOpen s ↔ IsOpen (f '' s) :=
  ⟨hf.isOpenMap s, fun h => by
    convert ← h.preimage hf.isEmbedding.continuous
    apply preimage_image_eq _ hf.inj⟩

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.open_iff_image_open := IsOpenEmbedding.open_iff_image_open

theorem IsOpenEmbedding.tendsto_nhds_iff [TopologicalSpace Z] {f : ι → Y} {l : Filter ι} {y : Y}
    (hg : IsOpenEmbedding g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.isEmbedding.tendsto_nhds_iff

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.tendsto_nhds_iff := IsOpenEmbedding.tendsto_nhds_iff

theorem IsOpenEmbedding.tendsto_nhds_iff' (hf : IsOpenEmbedding f) {l : Filter Z} {x : X} :
    Tendsto (g ∘ f) (𝓝 x) l ↔ Tendsto g (𝓝 (f x)) l := by
  rw [Tendsto, ← map_map, hf.map_nhds_eq]; rfl

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.tendsto_nhds_iff' := IsOpenEmbedding.tendsto_nhds_iff'

theorem IsOpenEmbedding.continuousAt_iff [TopologicalSpace Z] (hf : IsOpenEmbedding f) {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.continuousAt_iff := IsOpenEmbedding.continuousAt_iff

theorem IsOpenEmbedding.continuous (hf : IsOpenEmbedding f) : Continuous f :=
  hf.isEmbedding.continuous

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.continuous := IsOpenEmbedding.continuous

theorem IsOpenEmbedding.open_iff_preimage_open (hf : IsOpenEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.open_iff_image_open, image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.open_iff_preimage_open := IsOpenEmbedding.open_iff_preimage_open

lemma IsOpenEmbedding.of_isEmbedding_isOpenMap (h₁ : IsEmbedding f) (h₂ : IsOpenMap f) :
    IsOpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩

@[deprecated (since := "2024-10-18")]
alias openEmbedding_of_embedding_open := IsOpenEmbedding.of_isEmbedding_isOpenMap

/-- A surjective embedding is an `IsOpenEmbedding`. -/
lemma IsOpenEmbedding.of_isEmbedding (hf : IsEmbedding f) (hsurj : f.Surjective) :
    IsOpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

@[deprecated (since := "2024-10-18")]
alias _root_.Embedding.toOpenEmbedding_of_surjective := IsOpenEmbedding.of_isEmbedding

lemma isOpenEmbedding_iff_isEmbedding_isOpenMap : IsOpenEmbedding f ↔ IsEmbedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩

@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_embedding_open := isOpenEmbedding_iff_isEmbedding_isOpenMap

theorem isOpenEmbedding_of_continuous_injective_open
    (h₁ : Continuous f) (h₂ : Injective f) (h₃ : IsOpenMap f) : IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, inducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))

theorem isOpenEmbedding_iff_continuous_injective_open :
    IsOpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.inj, h.isOpenMap⟩, fun h =>
    isOpenEmbedding_of_continuous_injective_open h.1 h.2.1 h.2.2⟩

@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_continuous_injective_open := isOpenEmbedding_iff_continuous_injective_open

theorem isOpenEmbedding_id : IsOpenEmbedding (@id X) :=
  ⟨.id, IsOpenMap.id.isOpen_range⟩

@[deprecated (since := "2024-10-18")]
alias openEmbedding_id := isOpenEmbedding_id

namespace IsOpenEmbedding
variable [TopologicalSpace Z]

protected theorem comp (hg : IsOpenEmbedding g)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩

theorem isOpenMap_iff (hg : IsOpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, Filter.map_le_map_iff hg.inj]

theorem of_comp_iff (f : X → Y) (hg : IsOpenEmbedding g) :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_continuous_injective_open, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.inj.of_comp_iff]

theorem of_comp (f : X → Y) (hg : IsOpenEmbedding g)
    (h : IsOpenEmbedding (g ∘ f)) : IsOpenEmbedding f :=
  (IsOpenEmbedding.of_comp_iff f hg).1 h

theorem of_isEmpty [IsEmpty X] (f : X → Y) : IsOpenEmbedding f :=
  of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)

theorem image_mem_nhds {f : X → Y} (hf : IsOpenEmbedding f) {s : Set X} {x : X} :
    f '' s ∈ 𝓝 (f x) ↔ s ∈ 𝓝 x := by
  rw [← hf.map_nhds_eq, mem_map, preimage_image_eq _ hf.inj]

end IsOpenEmbedding

end IsOpenEmbedding

section IsClosedEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedEmbedding

lemma isEmbedding (hf : IsClosedEmbedding f) : IsEmbedding f := hf.toIsEmbedding
lemma inducing (hf : IsClosedEmbedding f) : Inducing f := hf.isEmbedding.toInducing
lemma continuous (hf : IsClosedEmbedding f) : Continuous f := hf.isEmbedding.continuous

lemma tendsto_nhds_iff {g : ι → X} {l : Filter ι} {x : X} (hf : IsClosedEmbedding f) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) := hf.isEmbedding.tendsto_nhds_iff

lemma isClosedMap (hf : IsClosedEmbedding f) : IsClosedMap f :=
  hf.isEmbedding.toInducing.isClosedMap hf.isClosed_range

theorem closed_iff_image_closed (hf : IsClosedEmbedding f) {s : Set X} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.inj]
    exact h.preimage hf.continuous⟩

theorem closed_iff_preimage_closed (hf : IsClosedEmbedding f) {s : Set Y}
    (hs : s ⊆ range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.closed_iff_image_closed, image_preimage_eq_of_subset hs]

lemma of_isEmbedding_isClosedMap (h₁ : IsEmbedding f) (h₂ : IsClosedMap f) :
    IsClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩

@[deprecated (since := "2024-10-20")]
alias _root_.closedEmbedding_of_embedding_closed := of_isEmbedding_isClosedMap

lemma _root_.IsClosedEmbedding.of_continuous_injective_isClosedMap (h₁ : Continuous f)
    (h₂ : Injective f) (h₃ : IsClosedMap f) : IsClosedEmbedding f := by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl, preimage_image_eq _ h₂, compl_compl]

@[deprecated (since := "2024-10-20")]
alias _root_.closedEmbedding_of_continuous_injective_closed :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap

theorem _root_.isClosedEmbedding_id : IsClosedEmbedding (@id X) :=
  ⟨.id, IsClosedMap.id.isClosed_range⟩

@[deprecated (since := "2024-10-20")]
alias _root_.closedEmbedding_id := _root_.isClosedEmbedding_id

theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (g ∘ f) :=
  ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩

lemma of_comp_iff (hg : IsClosedEmbedding g) : IsClosedEmbedding (g ∘ f) ↔ IsClosedEmbedding f := by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.closed_iff_image_closed]

theorem closure_image_eq (hf : IsClosedEmbedding f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

end IsClosedEmbedding

end IsClosedEmbedding
