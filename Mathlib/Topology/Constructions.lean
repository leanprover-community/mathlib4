/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Piecewise
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Curry
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.NhdsSet

/-!
# Constructions of new topological spaces from old ones

This file constructs pi types, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, subspace, quotient space

-/

noncomputable section

open Topology TopologicalSpace Set Filter Function
open scoped Set.Notation

universe u v u' v'

variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*}

section Constructions

instance {r : X → X → Prop} [t : TopologicalSpace X] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

instance instTopologicalSpaceQuotient {s : Setoid X} [t : TopologicalSpace X] :
    TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk' t

instance instTopologicalSpaceSigma {ι : Type*} {X : ι → Type v} [t₂ : ∀ i, TopologicalSpace (X i)] :
    TopologicalSpace (Sigma X) :=
  ⨆ i, coinduced (Sigma.mk i) (t₂ i)

instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f ↦ f i) (t₂ i)

instance ULift.topologicalSpace [t : TopologicalSpace X] : TopologicalSpace (ULift.{v, u} X) :=
  t.induced ULift.down

/-!
### `Additive`, `Multiplicative`

The topology on those type synonyms is inherited without change.
-/

section

variable [TopologicalSpace X]

open Additive Multiplicative

instance : TopologicalSpace (Additive X) := ‹TopologicalSpace X›
instance : TopologicalSpace (Multiplicative X) := ‹TopologicalSpace X›

instance [DiscreteTopology X] : DiscreteTopology (Additive X) := ‹DiscreteTopology X›
instance [DiscreteTopology X] : DiscreteTopology (Multiplicative X) := ‹DiscreteTopology X›

instance [CompactSpace X] : CompactSpace (Additive X) := ‹CompactSpace X›
instance [CompactSpace X] : CompactSpace (Multiplicative X) := ‹CompactSpace X›

instance [NoncompactSpace X] : NoncompactSpace (Additive X) := ‹NoncompactSpace X›
instance [NoncompactSpace X] : NoncompactSpace (Multiplicative X) := ‹NoncompactSpace X›

instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Additive X) :=
  ‹WeaklyLocallyCompactSpace X›
instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Multiplicative X) :=
  ‹WeaklyLocallyCompactSpace X›

instance [LocallyCompactSpace X] : LocallyCompactSpace (Additive X) := ‹LocallyCompactSpace X›
instance [LocallyCompactSpace X] : LocallyCompactSpace (Multiplicative X) := ‹LocallyCompactSpace X›

theorem continuous_ofMul : Continuous (ofMul : X → Additive X) := continuous_id

theorem continuous_toMul : Continuous (toMul : Additive X → X) := continuous_id

theorem continuous_ofAdd : Continuous (ofAdd : X → Multiplicative X) := continuous_id

theorem continuous_toAdd : Continuous (toAdd : Multiplicative X → X) := continuous_id

theorem isOpenMap_ofMul : IsOpenMap (ofMul : X → Additive X) := IsOpenMap.id

theorem isOpenMap_toMul : IsOpenMap (toMul : Additive X → X) := IsOpenMap.id

theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : X → Multiplicative X) := IsOpenMap.id

theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X → X) := IsOpenMap.id

theorem isClosedMap_ofMul : IsClosedMap (ofMul : X → Additive X) := IsClosedMap.id

theorem isClosedMap_toMul : IsClosedMap (toMul : Additive X → X) := IsClosedMap.id

theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : X → Multiplicative X) := IsClosedMap.id

theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X → X) := IsClosedMap.id

theorem nhds_ofMul (x : X) : 𝓝 (ofMul x) = map ofMul (𝓝 x) := rfl

theorem nhds_ofAdd (x : X) : 𝓝 (ofAdd x) = map ofAdd (𝓝 x) := rfl

theorem nhds_toMul (x : Additive X) : 𝓝 x.toMul = map toMul (𝓝 x) := rfl

theorem nhds_toAdd (x : Multiplicative X) : 𝓝 x.toAdd = map toAdd (𝓝 x) := rfl

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/


section

variable [TopologicalSpace X]

open OrderDual

instance OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ := ‹_›
instance OrderDual.instDiscreteTopology [DiscreteTopology X] : DiscreteTopology Xᵒᵈ := ‹_›

theorem continuous_toDual : Continuous (toDual : X → Xᵒᵈ) := continuous_id

theorem continuous_ofDual : Continuous (ofDual : Xᵒᵈ → X) := continuous_id

theorem isOpenMap_toDual : IsOpenMap (toDual : X → Xᵒᵈ) := IsOpenMap.id

theorem isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ → X) := IsOpenMap.id

theorem isClosedMap_toDual : IsClosedMap (toDual : X → Xᵒᵈ) := IsClosedMap.id

theorem isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ → X) := IsClosedMap.id

theorem nhds_toDual (x : X) : 𝓝 (toDual x) = map toDual (𝓝 x) := rfl

theorem nhds_ofDual (x : X) : 𝓝 (ofDual x) = map ofDual (𝓝 x) := rfl

variable [Preorder X] {x : X}

instance OrderDual.instNeBotNhdsWithinIoi [(𝓝[<] x).NeBot] : (𝓝[>] toDual x).NeBot := ‹_›
instance OrderDual.instNeBotNhdsWithinIio [(𝓝[>] x).NeBot] : (𝓝[<] toDual x).NeBot := ‹_›

end

theorem Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
    {x : X} (hs : V ∈ 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V ∈ 𝓝 x :=
  preimage_nhds_coinduced hs

/-- The image of a dense set under `Quotient.mk'` is a dense set. -/
theorem Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

/-- The composition of `Quotient.mk'` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y → X} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng

theorem continuous_map_of_le {α : Type*} [TopologicalSpace α]
    {s t : Setoid α} (h : s ≤ t) : Continuous (Setoid.map_of_le h) :=
  continuous_coinduced_rng

theorem continuous_map_sInf {α : Type*} [TopologicalSpace α]
    {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) : Continuous (Setoid.map_sInf h) :=
  continuous_coinduced_rng

instance {p : X → Prop} [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s _ ↦ ⟨(↑) '' s, isOpen_discrete _, preimage_image_eq _ Subtype.val_injective⟩⟩

instance Sum.discreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
    [hY : DiscreteTopology Y] : DiscreteTopology (X ⊕ Y) :=
  ⟨sup_eq_bot_iff.2 <| by simp [h.eq_bot, hY.eq_bot]⟩

instance Sigma.discreteTopology {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [h : ∀ i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y) :=
  ⟨iSup_eq_bot.2 fun _ ↦ by simp only [(h _).eq_bot, coinduced_bot]⟩

@[simp] lemma comap_nhdsWithin_range {α β} [TopologicalSpace β] (f : α → β) (y : β) :
    comap f (𝓝[range f] y) = comap f (𝓝 y) := comap_inf_principal_range

section Top

variable [TopologicalSpace X]

/-
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set X) (x : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 x ↔ ∃ u ∈ 𝓝 (x : X), Subtype.val ⁻¹' u ⊆ t :=
  mem_nhds_induced _ x t

theorem nhds_subtype (s : Set X) (x : { x // x ∈ s }) : 𝓝 x = comap (↑) (𝓝 (x : X)) :=
  nhds_induced _ x

lemma nhds_subtype_eq_comap_nhdsWithin (s : Set X) (x : { x // x ∈ s }) :
    𝓝 x = comap (↑) (𝓝[s] (x : X)) := by
  rw [nhds_subtype, ← comap_nhdsWithin_range, Subtype.range_val]

theorem nhdsWithin_subtype_eq_bot_iff {s t : Set X} {x : s} :
    𝓝[((↑) : s → X) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap, nhdsWithin, nhdsWithin, comap_inf, comap_principal,
    nhds_induced]

theorem nhds_ne_subtype_eq_bot_iff {S : Set X} {x : S} :
    𝓝[≠] x = ⊥ ↔ 𝓝[≠] (x : X) ⊓ 𝓟 S = ⊥ := by
  rw [← nhdsWithin_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
    Subtype.coe_injective.preimage_image]

theorem nhds_ne_subtype_neBot_iff {S : Set X} {x : S} :
    (𝓝[≠] x).NeBot ↔ (𝓝[≠] (x : X) ⊓ 𝓟 S).NeBot := by
  rw [neBot_iff, neBot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]

theorem discreteTopology_subtype_iff {S : Set X} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

end Top

/-- A type synonym equipped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def CofiniteTopology (X : Type*) := X

namespace CofiniteTopology

/-- The identity equivalence between `` and `CofiniteTopology `. -/
def of : X ≃ CofiniteTopology X :=
  Equiv.refl X

instance [Inhabited X] : Inhabited (CofiniteTopology X) where default := of default

instance : TopologicalSpace (CofiniteTopology X) where
  IsOpen s := s.Nonempty → Set.Finite sᶜ
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

theorem isOpen_iff {s : Set (CofiniteTopology X)} : IsOpen s ↔ s.Nonempty → sᶜ.Finite :=
  Iff.rfl

theorem isOpen_iff' {s : Set (CofiniteTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff {s : Set (CofiniteTopology X)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

theorem nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure x ⊔ cofinite := by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ ↦ hU', hU⟩

theorem mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem MapClusterPt.curry_prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la.curry lb) (.map f g) := by
  rw [mapClusterPt_iff_frequently] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx ↦ (hg t ht).mono fun y hy ↦ ⟨hx, hy⟩

theorem MapClusterPt.prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la ×ˢ lb) (.map f g) :=
  (hf.curry_prodMap hg).mono <| map_mono curry_le_prod

end Prod

section Bool

lemma continuous_bool_rng [TopologicalSpace X] {f : X → Bool} (b : Bool) :
    Continuous f ↔ IsClopen (f ⁻¹' {b}) := by
  rw [continuous_discrete_rng, Bool.forall_bool' b, IsClopen, ← isOpen_compl_iff, ← preimage_compl,
    Bool.compl_singleton, and_comm]

end Bool

section Subtype

variable [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop}

lemma Topology.IsInducing.subtypeVal {t : Set Y} : IsInducing ((↑) : t → Y) := ⟨rfl⟩

lemma Topology.IsInducing.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (h : IsInducing (t.codRestrict f ht)) : IsInducing f := subtypeVal.comp h

lemma Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, Subtype.coe_injective⟩

theorem Topology.IsClosedEmbedding.subtypeVal (h : IsClosed {a | p a}) :
    IsClosedEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[continuity, fun_prop]
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom

theorem Continuous.subtype_val {f : Y → Subtype p} (hf : Continuous f) :
    Continuous fun x ↦ (f x : X) :=
  continuous_subtype_val.comp hf

theorem IsOpen.isOpenEmbedding_subtypeVal {s : Set X} (hs : IsOpen s) :
    IsOpenEmbedding ((↑) : s → X) :=
  ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩

theorem IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) : s → X) :=
  hs.isOpenEmbedding_subtypeVal.isOpenMap

theorem IsOpenMap.restrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
    IsOpenMap (s.restrict f) :=
  hf.comp hs.isOpenMap_subtype_val

lemma IsClosed.isClosedEmbedding_subtypeVal {s : Set X} (hs : IsClosed s) :
    IsClosedEmbedding ((↑) : s → X) := .subtypeVal hs

theorem IsClosed.isClosedMap_subtype_val {s : Set X} (hs : IsClosed s) :
    IsClosedMap ((↑) : s → X) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap

@[continuity, fun_prop]
theorem Continuous.subtype_mk {f : Y → X} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x ↦ (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h

theorem Continuous.subtype_map {f : X → Y} (h : Continuous f) {q : Y → Prop}
    (hpq : ∀ x, p x → q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_val).subtype_mk _

theorem continuous_inclusion {s t : Set X} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_id.subtype_map h

theorem continuousAt_subtype_val {p : X → Prop} {x : Subtype p} :
    ContinuousAt ((↑) : Subtype p → X) x :=
  continuous_subtype_val.continuousAt

theorem Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔ s ⊆ closure ((↑) '' t) := by
  rw [IsInducing.subtypeVal.dense_iff, SetCoe.forall]
  rfl

theorem map_nhds_subtype_val {s : Set X} (x : s) : map ((↑) : s → X) (𝓝 x) = 𝓝[s] ↑x := by
  rw [IsInducing.subtypeVal.map_nhds_eq, Subtype.range_val]

theorem map_nhds_subtype_coe_eq_nhds {x : X} (hx : p x) (h : ∀ᶠ x in 𝓝 x, p x) :
    map ((↑) : Subtype p → X) (𝓝 ⟨x, hx⟩) = 𝓝 x :=
  map_nhds_induced_of_mem <| by rw [Subtype.range_val]; exact h

theorem nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x) :=
  nhds_induced _ _

theorem tendsto_subtype_rng {Y : Type*} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p} :
    ∀ {x : Subtype p}, Tendsto f l (𝓝 x) ↔ Tendsto (fun x ↦ (f x : X)) l (𝓝 (x : X))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; rfl

theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ closure s ↔ (x : X) ∈ closure (((↑) : _ → X) '' s) :=
  closure_induced

@[simp]
theorem continuousAt_codRestrict_iff {f : X → Y} {t : Set Y} (h1 : ∀ x, f x ∈ t) {x : X} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x :=
  IsInducing.subtypeVal.continuousAt_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff

theorem ContinuousAt.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuousAt_subtype_val).codRestrict _

theorem ContinuousAt.restrictPreimage {f : X → Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x) :
    ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _

@[continuity, fun_prop]
theorem Continuous.codRestrict {f : X → Y} {s : Set Y} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs

@[continuity, fun_prop]
theorem Continuous.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
    (h2 : Continuous f) : Continuous (h1.restrict f s t) :=
  (h2.comp continuous_subtype_val).codRestrict _

@[continuity, fun_prop]
theorem Continuous.restrictPreimage {f : X → Y} {s : Set Y} (h : Continuous f) :
    Continuous (s.restrictPreimage f) :=
  h.restrict _

lemma Topology.IsEmbedding.restrict {f : X → Y}
    (hf : IsEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) :
    IsEmbedding H.restrict :=
  .of_comp (hf.continuous.restrict H) continuous_subtype_val (hf.comp .subtypeVal)

lemma Topology.IsOpenEmbedding.restrict {f : X → Y}
    (hf : IsOpenEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) (hs : IsOpen s) :
    IsOpenEmbedding H.restrict :=
  ⟨hf.isEmbedding.restrict H, (by
    rw [MapsTo.range_restrict]
    exact continuous_subtype_val.1 _ (hf.isOpenMap _ hs))⟩

theorem Topology.IsInducing.codRestrict {e : X → Y} (he : IsInducing e) {s : Set Y}
    (hs : ∀ x, e x ∈ s) : IsInducing (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

protected lemma Topology.IsEmbedding.codRestrict {e : X → Y} (he : IsEmbedding e) (s : Set Y)
    (hs : ∀ x, e x ∈ s) : IsEmbedding (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

variable {s t : Set X}

protected lemma Topology.IsEmbedding.inclusion (h : s ⊆ t) :
    IsEmbedding (inclusion h) := IsEmbedding.subtypeVal.codRestrict _ _

protected lemma Topology.IsOpenEmbedding.inclusion (hst : s ⊆ t) (hs : IsOpen (t ↓∩ s)) :
    IsOpenEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isOpen_range := by rwa [range_inclusion]

protected lemma Topology.IsClosedEmbedding.inclusion (hst : s ⊆ t) (hs : IsClosed (t ↓∩ s)) :
    IsClosedEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isClosed_range := by rwa [range_inclusion]

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete. -/
theorem DiscreteTopology.of_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (_ : DiscreteTopology s) (ts : t ⊆ s) : DiscreteTopology t :=
  (IsEmbedding.inclusion ts).discreteTopology

/-- Let `s` be a discrete subset of a topological space. Then the preimage of `s` by
a continuous injective map is also discrete. -/
theorem DiscreteTopology.preimage_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Set Y) [DiscreteTopology s] {f : X → Y} (hc : Continuous f)
    (hinj : Function.Injective f) : DiscreteTopology (f ⁻¹' s) :=
  DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x ↦ x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)

/-- If `f : X → Y` is a quotient map,
then its restriction to the preimage of an open set is a quotient map too. -/
theorem Topology.IsQuotientMap.restrictPreimage_isOpen {f : X → Y} (hf : IsQuotientMap f)
    {s : Set Y} (hs : IsOpen s) : IsQuotientMap (s.restrictPreimage f) := by
  refine isQuotientMap_iff.2 ⟨hf.surjective.restrictPreimage _, fun U ↦ ?_⟩
  rw [hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, ← hf.isOpen_preimage,
    (hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_val_preimage_restrictPreimage]

open scoped Set.Notation in
lemma isClosed_preimage_val {s t : Set X} : IsClosed (s ↓∩ t) ↔ s ∩ closure (s ∩ t) ⊆ t := by
  rw [← closure_eq_iff_isClosed, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    ← Subtype.val_injective.image_injective.eq_iff, Subtype.image_preimage_coe,
    Subtype.image_preimage_coe, subset_antisymm_iff, and_iff_left, Set.subset_inter_iff,
    and_iff_right]
  exacts [Set.inter_subset_left, Set.subset_inter Set.inter_subset_left subset_closure]

theorem frontier_inter_open_inter {s t : Set X} (ht : IsOpen t) :
    frontier (s ∩ t) ∩ t = frontier s ∩ t := by
  simp only [Set.inter_comm _ t, ← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_self_inter]

section SetNotation

open scoped Set.Notation

lemma IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) : IsOpen (s ↓∩ t) :=
  ht.preimage continuous_subtype_val

lemma IsClosed.preimage_val {s t : Set X} (ht : IsClosed t) : IsClosed (s ↓∩ t) :=
  ht.preimage continuous_subtype_val

@[simp] lemma IsOpen.inter_preimage_val_iff {s t : Set X} (hs : IsOpen s) :
    IsOpen (s ↓∩ t) ↔ IsOpen (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isOpenMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

@[simp] lemma IsClosed.inter_preimage_val_iff {s t : Set X} (hs : IsClosed s) :
    IsClosed (s ↓∩ t) ↔ IsClosed (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isClosedMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

end SetNotation

end Subtype

section Quotient

variable [TopologicalSpace X] [TopologicalSpace Y]
variable {r : X → X → Prop} {s : Setoid X}

theorem isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X r) :=
  ⟨Quot.exists_rep, rfl⟩

@[continuity, fun_prop]
theorem continuous_quot_mk : Continuous (@Quot.mk X r) :=
  continuous_coinduced_rng

@[continuity, fun_prop]
theorem continuous_quot_lift {f : X → Y} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → Y) :=
  continuous_coinduced_dom.2 h

theorem isQuotientMap_quotient_mk' : IsQuotientMap (@Quotient.mk' X s) :=
  isQuotientMap_quot_mk

theorem continuous_quotient_mk' : Continuous (@Quotient.mk' X s) :=
  continuous_coinduced_rng

theorem Continuous.quotient_lift {f : X → Y} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → Y) :=
  continuous_coinduced_dom.2 h

theorem Continuous.quotient_liftOn' {f : X → Y} (h : Continuous f)
    (hs : ∀ a b, s a b → f a = f b) :
    Continuous (fun x ↦ Quotient.liftOn' x f hs : Quotient s → Y) :=
  h.quotient_lift hs

open scoped Relator in
@[continuity, fun_prop]
theorem Continuous.quotient_map' {t : Setoid Y} {f : X → Y} (hf : Continuous f)
    (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _

end Quotient

section Pi

variable {ι : Type*} {A : ι → Type*} {κ : Type*} [TopologicalSpace X]
  [T : ∀ i, TopologicalSpace (A i)] {f : X → ∀ i : ι, A i}

theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a ↦ f a i := by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]
theorem continuous_pi (h : ∀ i, Continuous fun a ↦ f a i) : Continuous f :=
  continuous_pi_iff.2 h

@[continuity, fun_prop]
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, A i ↦ p i :=
  continuous_iInf_dom continuous_induced_dom

@[continuity]
theorem continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i ↦ p j i :=
  (continuous_apply i).comp (continuous_apply j)

theorem continuousAt_apply (i : ι) (x : ∀ i, A i) : ContinuousAt (fun p : ∀ i, A i ↦ p i) x :=
  (continuous_apply i).continuousAt

theorem Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y → ∀ i, A i} {x : ∀ i, A i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a ↦ f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).tendsto.comp h

@[fun_prop]
protected theorem Continuous.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, A i → Y i} (hf : ∀ i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i ↦ (hf i).comp (continuous_apply i)

theorem nhds_pi {a : ∀ i, A i} : 𝓝 a = pi fun i ↦ 𝓝 (a i) := by
  simp only [nhds_iInf, nhds_induced, Filter.pi]

protected theorem IsOpenMap.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f : ∀ i, A i → Y i}
    (hfo : ∀ i, IsOpenMap (f i)) (hsurj : ∀ᶠ i in cofinite, Surjective (f i)) :
    IsOpenMap (Pi.map f) := by
  refine IsOpenMap.of_nhds_le fun x ↦ ?_
  rw [nhds_pi, nhds_pi, map_piMap_pi hsurj]
  exact Filter.pi_mono fun i ↦ (hfo i).nhds_le _

protected theorem IsOpenQuotientMap.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, A i → Y i} (hf : ∀ i, IsOpenQuotientMap (f i)) : IsOpenQuotientMap (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2, .piMap (fun i ↦ (hf i).3) <|
    .of_forall fun i ↦ (hf i).1⟩

theorem tendsto_pi_nhds {f : Y → ∀ i, A i} {g : ∀ i, A i} {u : Filter Y} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i ↦ f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]

theorem continuousAt_pi {f : X → ∀ i, A i} {x : X} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y ↦ f y i) x :=
  tendsto_pi_nhds

@[fun_prop]
theorem continuousAt_pi' {f : X → ∀ i, A i} {x : X} (hf : ∀ i, ContinuousAt (fun y ↦ f y i) x) :
    ContinuousAt f x :=
  continuousAt_pi.2 hf

@[fun_prop]
protected theorem ContinuousAt.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, A i → Y i} {x : ∀ i, A i} (hf : ∀ i, ContinuousAt (f i) (x i)) :
    ContinuousAt (Pi.map f) x :=
  continuousAt_pi.2 fun i ↦ (hf i).comp (continuousAt_apply i x)

theorem Pi.continuous_precomp' {ι' : Type*} (φ : ι' → ι) :
    Continuous (fun (f : (∀ i, A i)) (j : ι') ↦ f (φ j)) :=
  continuous_pi fun j ↦ continuous_apply (φ j)

theorem Pi.continuous_precomp {ι' : Type*} (φ : ι' → ι) :
    Continuous (· ∘ φ : (ι → X) → (ι' → X)) :=
  Pi.continuous_precomp' φ

theorem Pi.continuous_postcomp' {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {g : ∀ i, A i → X i} (hg : ∀ i, Continuous (g i)) :
    Continuous (fun (f : (∀ i, A i)) (i : ι) ↦ g i (f i)) :=
  continuous_pi fun i ↦ (hg i).comp <| continuous_apply i

theorem Pi.continuous_postcomp [TopologicalSpace Y] {g : X → Y} (hg : Continuous g) :
    Continuous (g ∘ · : (ι → X) → (ι → Y)) :=
  Pi.continuous_postcomp' fun _ ↦ hg

lemma Pi.induced_precomp' {ι' : Type*} (φ : ι' → ι) :
    induced (fun (f : (∀ i, A i)) (j : ι') ↦ f (φ j)) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) (T (φ i')) := by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]

lemma Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' → ι) :
    induced (· ∘ φ) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y› :=
  induced_precomp' φ

@[continuity, fun_prop]
lemma Pi.continuous_restrict (S : Set ι) :
    Continuous (S.restrict : (∀ i : ι, A i) → (∀ i : S, A i)) :=
  Pi.continuous_precomp' ((↑) : S → ι)

@[continuity, fun_prop]
lemma Pi.continuous_restrict₂ {s t : Set ι} (hst : s ⊆ t) : Continuous (restrict₂ (π := A) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

@[continuity, fun_prop]
theorem Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π := A)) :=
  continuous_pi fun _ ↦ continuous_apply _

@[continuity, fun_prop]
theorem Finset.continuous_restrict₂ {s t : Finset ι} (hst : s ⊆ t) :
    Continuous (Finset.restrict₂ (π := A) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

variable [TopologicalSpace Z]

@[continuity, fun_prop]
theorem Pi.continuous_restrict_apply (s : Set X) {f : X → Z} (hf : Continuous f) :
    Continuous (s.restrict f) := hf.comp continuous_subtype_val

@[continuity, fun_prop]
theorem Pi.continuous_restrict₂_apply {s t : Set X} (hst : s ⊆ t)
    {f : t → Z} (hf : Continuous f) :
    Continuous (restrict₂ (π := fun _ ↦ Z) hst f) := hf.comp (continuous_inclusion hst)

@[continuity, fun_prop]
theorem Finset.continuous_restrict_apply (s : Finset X) {f : X → Z} (hf : Continuous f) :
    Continuous (s.restrict f) := hf.comp continuous_subtype_val

@[continuity, fun_prop]
theorem Finset.continuous_restrict₂_apply {s t : Finset X} (hst : s ⊆ t)
    {f : t → Z} (hf : Continuous f) :
    Continuous (restrict₂ (π := fun _ ↦ Z) hst f) := hf.comp (continuous_inclusion hst)

lemma Pi.induced_restrict (S : Set ι) :
    induced (S.restrict) Pi.topologicalSpace =
    ⨅ i ∈ S, induced (eval i) (T i) := by
  simp +unfoldPartialApp [← iInf_subtype'', ← induced_precomp' ((↑) : S → ι),
    restrict]

lemma Pi.induced_restrict_sUnion (𝔖 : Set (Set ι)) :
    induced (⋃₀ 𝔖).restrict (Pi.topologicalSpace (Y := fun i : (⋃₀ 𝔖) ↦ A i)) =
    ⨅ S ∈ 𝔖, induced S.restrict Pi.topologicalSpace := by
  simp_rw [Pi.induced_restrict, iInf_sUnion]

theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter Y} {f : Y → ∀ i, A i} {x : ∀ i, A i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : Y → A i} {xi : A i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a ↦ update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j ↦ by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

theorem ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X → A i}
    (hg : ContinuousAt g x) : ContinuousAt (fun a ↦ update (f a) i (g a)) x :=
  hf.tendsto.update i hg

theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X → A i}
    (hg : Continuous g) : Continuous fun a ↦ update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.update i hg.continuousAt

/-- `Function.update f i x` is continuous in `(f, x)`. -/
@[continuity, fun_prop]
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, A j) × A i ↦ update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

/-- `Pi.mulSingle i x` is continuous in `x`. -/
@[to_additive (attr := continuity) /-- `Pi.single i x` is continuous in `x`. -/]
theorem continuous_mulSingle [∀ i, One (A i)] [DecidableEq ι] (i : ι) :
    Continuous fun x ↦ (Pi.mulSingle i x : ∀ i, A i) :=
  continuous_const.update _ continuous_id

section Fin
variable {n : ℕ} {A : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (A i)]

theorem Filter.Tendsto.finCons
    {f : Y → A 0} {g : Y → ∀ j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : ∀ j, A (Fin.succ j)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a ↦ Fin.cons (f a) (g a)) l (𝓝 <| Fin.cons x y) :=
  tendsto_pi_nhds.2 fun j ↦ Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

theorem ContinuousAt.finCons {f : X → A 0} {g : X → ∀ j : Fin n, A (Fin.succ j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ Fin.cons (f a) (g a)) x :=
  hf.tendsto.finCons hg

theorem Continuous.finCons {f : X → A 0} {g : X → ∀ j : Fin n, A (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a ↦ Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finCons hg.continuousAt

theorem Filter.Tendsto.matrixVecCons
    {f : Y → Z} {g : Y → Fin n → Z} {l : Filter Y} {x : Z} {y : Fin n → Z}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a ↦ Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y) :=
  hf.finCons hg

theorem ContinuousAt.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ Matrix.vecCons (f a) (g a)) x :=
  hf.finCons hg

theorem Continuous.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a ↦ Matrix.vecCons (f a) (g a) :=
  hf.finCons hg

theorem Filter.Tendsto.finSnoc
    {f : Y → ∀ j : Fin n, A j.castSucc} {g : Y → A (Fin.last _)}
    {l : Filter Y} {x : ∀ j, A (Fin.castSucc j)} {y : A (Fin.last _)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a ↦ Fin.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y) :=
  tendsto_pi_nhds.2 fun j ↦ Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

theorem ContinuousAt.finSnoc {f : X → ∀ j : Fin n, A j.castSucc} {g : X → A (Fin.last _)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ Fin.snoc (f a) (g a)) x :=
  hf.tendsto.finSnoc hg

theorem Continuous.finSnoc {f : X → ∀ j : Fin n, A j.castSucc} {g : X → A (Fin.last _)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a ↦ Fin.snoc (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finSnoc hg.continuousAt

theorem Filter.Tendsto.finInsertNth
    (i : Fin (n + 1)) {f : Y → A i} {g : Y → ∀ j : Fin n, A (i.succAbove j)} {l : Filter Y}
    {x : A i} {y : ∀ j, A (i.succAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a ↦ i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j ↦ Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

theorem ContinuousAt.finInsertNth
    (i : Fin (n + 1)) {f : X → A i} {g : X → ∀ j : Fin n, A (i.succAbove j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ i.insertNth (f a) (g a)) x :=
  hf.tendsto.finInsertNth i hg

theorem Continuous.finInsertNth
    (i : Fin (n + 1)) {f : X → A i} {g : X → ∀ j : Fin n, A (i.succAbove j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a ↦ i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finInsertNth i hg.continuousAt

theorem Filter.Tendsto.finInit {f : Y → ∀ j : Fin (n + 1), A j} {l : Filter Y} {x : ∀ j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a ↦ Fin.init (f a)) l (𝓝 <| Fin.init x) :=
  tendsto_pi_nhds.2 fun j ↦ apply_nhds hg j.castSucc

@[fun_prop]
theorem ContinuousAt.finInit {f : X → ∀ j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a ↦ Fin.init (f a)) x :=
  hf.tendsto.finInit

@[fun_prop]
theorem Continuous.finInit {f : X → ∀ j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a ↦ Fin.init (f a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finInit

theorem Filter.Tendsto.finTail {f : Y → ∀ j : Fin (n + 1), A j} {l : Filter Y} {x : ∀ j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a ↦ Fin.tail (f a)) l (𝓝 <| Fin.tail x) :=
  tendsto_pi_nhds.2 fun j ↦ apply_nhds hg j.succ

@[fun_prop]
theorem ContinuousAt.finTail {f : X → ∀ j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a ↦ Fin.tail (f a)) x :=
  hf.tendsto.finTail

@[fun_prop]
theorem Continuous.finTail {f : X → ∀ j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a ↦ Fin.tail (f a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finTail

end Fin

theorem isOpen_set_pi {i : Set ι} {s : ∀ a, Set (A a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha ↦ (hs _ ha).preimage (continuous_apply _)

theorem isOpen_pi_iff {s : Set (∀ a, A a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ (I : Finset ι) (u : ∀ a, Set (A a)),
        (∀ a, a ∈ I → IsOpen (u a) ∧ f a ∈ u a) ∧ (I : Set ι).pi u ⊆ s := by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ ↦ ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine ⟨I, fun a ↦ eval a '' (I : Set ι).pi fun a ↦ (h1 a).choose, fun i hi ↦ ?_, ?_⟩
    · simp_rw [eval_image_pi (Finset.mem_coe.mpr hi)
          (pi_nonempty_iff.mpr fun i ↦ ⟨_, fun _ ↦ (h1 i).choose_spec.2.2⟩)]
      exact (h1 i).choose_spec.2
    · exact Subset.trans
        (pi_mono fun i hi ↦ (eval_image_pi_subset hi).trans (h1 i).choose_spec.1) h2
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    classical
    refine ⟨I, fun a ↦ ite (a ∈ I) (t a) univ, fun i ↦ ?_, ?_⟩
    · by_cases hi : i ∈ I
      · use t i
        simp_rw [if_pos hi]
        exact ⟨Subset.rfl, (h1 i) hi⟩
      · use univ
        simp_rw [if_neg hi]
        exact ⟨Subset.rfl, isOpen_univ, mem_univ _⟩
    · rw [← univ_pi_ite]
      simp only [← ite_and, ← Finset.mem_coe, and_self_iff, univ_pi_ite, h2]

theorem isOpen_pi_iff' [Finite ι] {s : Set (∀ a, A a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ u : ∀ a, Set (A a), (∀ a, IsOpen (u a) ∧ f a ∈ u a) ∧ univ.pi u ⊆ s := by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ ↦ ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine
      ⟨fun i ↦ (h1 i).choose,
        ⟨fun i ↦ (h1 i).choose_spec.2,
          (pi_mono fun i _ ↦ (h1 i).choose_spec.1).trans (Subset.trans ?_ h2)⟩⟩
    rw [← pi_inter_compl (I : Set ι)]
    exact inter_subset_left
  · exact fun ⟨u, ⟨h1, _⟩⟩ ↦
      ⟨Finset.univ, u, ⟨fun i ↦ ⟨u i, ⟨rfl.subset, h1 i⟩⟩, by rwa [Finset.coe_univ]⟩⟩

theorem isClosed_set_pi {i : Set ι} {s : ∀ a, Set (A a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def]; exact isClosed_biInter fun a ha ↦ (hs _ ha).preimage (continuous_apply _)

theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (A i)} (a : ∀ i, A i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi

theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (A a)} {x : ∀ a, A a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, biInter_mem hi]
  exact fun a ha ↦ (continuous_apply a).continuousAt (hs a ha)

theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (A i)} (a : ∀ i, A i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]

theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (A i)} :
    interior (pi I s) = I.pi fun i ↦ interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, A a)} {x : ∀ a, A a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, A a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi ↦ ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

theorem pi_generateFrom_eq {A : ι → Type*} {g : ∀ a, Set (Set (A a))} :
    (@Pi.topologicalSpace ι A fun a ↦ generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (A a)) (i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    letI := fun a ↦ generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha ↦ GenerateOpen.basic _ (hi a ha))
  · classical
    refine le_iInf fun i ↦ coinduced_le_iff_le_induced.1 <| le_generateFrom fun s hs ↦ ?_
    refine GenerateOpen.basic _ ⟨update (fun i ↦ univ) i s, {i}, ?_⟩
    simp [hs]

theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (A a)) (i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι A fun _ ↦ generateFrom { s | IsOpen s } := by
    simp only [generateFrom_setOf_isOpen]
  _ = _ := pi_generateFrom_eq

theorem pi_generateFrom_eq_finite {X : ι → Type*} {g : ∀ a, Set (Set (X a))} [Finite ι]
    (hg : ∀ a, ⋃₀ g a = univ) :
    (@Pi.topologicalSpace ι X fun a ↦ generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (X a), (∀ a, s a ∈ g a) ∧ t = pi univ s } := by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ ↦ ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    letI := generateFrom { t | ∃ s : ∀ a, Set (X a), (∀ a, s a ∈ g a) ∧ t = pi univ s }
    refine isOpen_iff_forall_mem_open.2 fun f hf ↦ ?_
    choose c hcg hfc using fun a ↦ sUnion_eq_univ_iff.1 (hg a) (f a)
    refine ⟨pi i t ∩ pi ((↑i)ᶜ : Set ι) c, inter_subset_left, ?_, ⟨hf, fun a _ ↦ hfc a⟩⟩
    classical
    rw [← univ_pi_piecewise]
    refine GenerateOpen.basic _ ⟨_, fun a ↦ ?_, rfl⟩
    by_cases a ∈ i <;> simp [*]

theorem induced_to_pi {X : Type*} (f : X → ∀ i, A i) :
    induced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance := by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/-- Suppose `A i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → A i` for every `i : ι`, hence inducing a
map `g : X → Π i, A i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, A i`
where `Π i, A i` is endowed with the usual product topology. -/
theorem inducing_iInf_to_pi {X : Type*} (f : ∀ i, X → A i) :
    @IsInducing X (∀ i, A i) (⨅ i, induced (f i) inferInstance) _ fun x i ↦ f i x :=
  letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

variable [Finite ι] [∀ i, DiscreteTopology (A i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discreteTopology : DiscreteTopology (∀ i, A i) :=
  singletons_open_iff_discrete.mp fun x ↦ by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ ↦ (isOpen_discrete {x i})

lemma Function.Surjective.isEmbedding_comp {n m : Type*} (f : m → n) (hf : Function.Surjective f) :
    IsEmbedding ((· ∘ f) : (n → X) → (m → X)) := by
  refine ⟨isInducing_iff_nhds.mpr fun x ↦ ?_, hf.injective_comp_right⟩
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, ← hf.iInf_congr, Filter.comap_comap,
    Function.comp_def]

end Pi

section Sigma

variable {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*} [∀ i, TopologicalSpace (σ i)]
  [∀ k, TopologicalSpace (τ k)] [TopologicalSpace X]

@[continuity, fun_prop]
theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_iSup_rng continuous_coinduced_rng

theorem isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  rw [isOpen_iSup_iff]
  rfl

theorem isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]

theorem isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty

theorem isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sigma.mk ι σ i)) :=
  isOpenMap_sigmaMk.isOpen_range

theorem isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty

theorem isClosed_range_sigmaMk {i : ι} : IsClosed (range (@Sigma.mk ι σ i)) :=
  isClosedMap_sigmaMk.isClosed_range

lemma Topology.IsOpenEmbedding.sigmaMk {i : ι} : IsOpenEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk

lemma Topology.IsClosedEmbedding.sigmaMk {i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk

lemma Topology.IsEmbedding.sigmaMk {i : ι} : IsEmbedding (@Sigma.mk ι σ i) :=
  IsClosedEmbedding.sigmaMk.1

theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x) :=
  (IsOpenEmbedding.sigmaMk.map_nhds_eq x).symm

theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2) := by
  cases x
  apply Sigma.nhds_mk

theorem comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (IsEmbedding.sigmaMk.nhds_eq_comap _).symm

theorem isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a)) := by
  rw [← biUnion_of_singleton s, preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ ↦ isOpen_range_sigmaMk

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
theorem continuous_sigma_iff {f : Sigma σ → X} :
    Continuous f ↔ ∀ i, Continuous fun a ↦ f ⟨i, a⟩ := by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ ↦ continuous_coinduced_dom

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity, fun_prop]
theorem continuous_sigma {f : Sigma σ → X} (hf : ∀ i, Continuous fun a ↦ f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf

/-- A map defined on a sigma type (a.k.a. the disjoint union of an indexed family of topological
spaces) is inducing iff its restriction to each component is inducing and each the image of each
component under `f` can be separated from the images of all other components by an open set. -/
theorem inducing_sigma {f : Sigma σ → X} :
    IsInducing f ↔ (∀ i, IsInducing (f ∘ Sigma.mk i)) ∧
      (∀ i, ∃ U, IsOpen U ∧ ∀ x, f x ∈ U ↔ x.1 = i) := by
  refine ⟨fun h ↦ ⟨fun i ↦ h.comp IsEmbedding.sigmaMk.1, fun i ↦ ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [Set.ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ ↦ isInducing_iff_nhds.2 fun ⟨i, x⟩ ↦ ?_
    rw [Sigma.nhds_mk, (h₁ i).nhds_eq_comap, comp_apply, ← comap_comap, map_comap_of_mem]
    rcases h₂ i with ⟨U, hUo, hU⟩
    filter_upwards [preimage_mem_comap <| hUo.mem_nhds <| (hU _).2 rfl] with y hy
    simpa [hU] using hy

@[simp 1100]
theorem continuous_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ ∀ i, Continuous (f₂ i) :=
  continuous_sigma_iff.trans <| by
    simp only [Sigma.map, IsEmbedding.sigmaMk.continuous_iff, comp_def]

@[continuity, fun_prop]
theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf

theorem isOpenMap_sigma {f : Sigma σ → X} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a ↦ f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]

theorem isOpenMap_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  isOpenMap_sigma.trans <|
    forall_congr' fun i ↦ (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm

lemma Topology.isInducing_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h₁ : Injective f₁) : IsInducing (Sigma.map f₁ f₂) ↔ ∀ i, IsInducing (f₂ i) := by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]

lemma Topology.isEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h : Injective f₁) : IsEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsEmbedding (f₂ i) := by
  simp only [isEmbedding_iff, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]

lemma Topology.isOpenEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    IsOpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenEmbedding (f₂ i) := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

end Sigma

section ULift

theorem ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsOpen s ↔ IsOpen (ULift.up ⁻¹' s) := by
  rw [ULift.topologicalSpace, ← Equiv.ulift_apply, ← Equiv.ulift.coinduced_symm, ← isOpen_coinduced]

theorem ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsClosed s ↔ IsClosed (ULift.up ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_iff, preimage_compl]

@[continuity, fun_prop]
theorem continuous_uliftDown [TopologicalSpace X] : Continuous (ULift.down : ULift.{v, u} X → X) :=
  continuous_induced_dom

@[continuity, fun_prop]
theorem continuous_uliftUp [TopologicalSpace X] : Continuous (ULift.up : X → ULift.{v, u} X) :=
  continuous_induced_rng.2 continuous_id

@[deprecated (since := "2025-02-10")] alias continuous_uLift_down := continuous_uliftDown
@[deprecated (since := "2025-02-10")] alias continuous_uLift_up := continuous_uliftUp

@[continuity, fun_prop]
theorem continuous_uliftMap [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (ULift.map f : ULift.{u'} X → ULift.{v'} Y) := by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  fun_prop

lemma Topology.IsEmbedding.uliftDown [TopologicalSpace X] :
    IsEmbedding (ULift.down : ULift.{v, u} X → X) := ⟨⟨rfl⟩, ULift.down_injective⟩

lemma Topology.IsClosedEmbedding.uliftDown [TopologicalSpace X] :
    IsClosedEmbedding (ULift.down : ULift.{v, u} X → X) :=
  ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩

instance [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (ULift X) :=
  IsEmbedding.uliftDown.discreteTopology

end ULift

section Monad

variable [TopologicalSpace X] {s : Set X} {t : Set s}

theorem IsOpen.trans (ht : IsOpen t) (hs : IsOpen s) : IsOpen (t : Set X) := by
  rcases isOpen_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

theorem IsClosed.trans (ht : IsClosed t) (hs : IsClosed s) : IsClosed (t : Set X) := by
  rcases isClosed_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

end Monad

section NhdsSet
variable [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {t : Set Y}

/-- The product of a neighborhood of `s` and a neighborhood of `t` is a neighborhood of `s ×ˢ t`,
formulated in terms of a filter inequality. -/
theorem nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) ≤ 𝓝ˢ s ×ˢ 𝓝ˢ t :=
  ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ ↦
    (huo.prod hvo).mem_nhdsSet.2 <| prod_mono hsu htv

theorem Filter.eventually_nhdsSet_prod_iff {p : X × Y → Prop} :
    (∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q) ↔
      ∀ x ∈ s, ∀ y ∈ t,
          ∃ px : X → Prop, (∀ᶠ x' in 𝓝 x, px x') ∧ ∃ py : Y → Prop, (∀ᶠ y' in 𝓝 y, py y') ∧
            ∀ {x : X}, px x → ∀ {y : Y}, py y → p (x, y) := by
  simp_rw [eventually_nhdsSet_iff_forall, forall_prod_set, nhds_prod_eq, eventually_prod_iff]

theorem Filter.Eventually.prod_nhdsSet {p : X × Y → Prop} {px : X → Prop} {py : Y → Prop}
    (hp : ∀ {x : X}, px x → ∀ {y : Y}, py y → p (x, y)) (hs : ∀ᶠ x in 𝓝ˢ s, px x)
    (ht : ∀ᶠ y in 𝓝ˢ t, py y) : ∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q :=
  nhdsSet_prod_le _ _ (mem_of_superset (prod_mem_prod hs ht) fun _ ⟨hx, hy⟩ ↦ hp hx hy)

end NhdsSet
