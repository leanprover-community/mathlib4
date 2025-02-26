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
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.NhdsSet

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
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

product, sum, disjoint union, subspace, quotient space

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

instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance instTopologicalSpaceSigma {ι : Type*} {X : ι → Type v} [t₂ : ∀ i, TopologicalSpace (X i)] :
    TopologicalSpace (Sigma X) :=
  ⨆ i, coinduced (Sigma.mk i) (t₂ i)

instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)

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
  ⟨bot_unique fun s _ => ⟨(↑) '' s, isOpen_discrete _, preimage_image_eq _ Subtype.val_injective⟩⟩

instance Sum.discreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
    [hY : DiscreteTopology Y] : DiscreteTopology (X ⊕ Y) :=
  ⟨sup_eq_bot_iff.2 <| by simp [h.eq_bot, hY.eq_bot]⟩

instance Sigma.discreteTopology {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [h : ∀ i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y) :=
  ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩

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
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

theorem mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Lean 4 fails to deduce implicit args
@[simp] theorem continuous_prod_mk {f : X → Y} {g : X → Z} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  (@continuous_inf_rng X (Y × Z) _ _ (TopologicalSpace.induced Prod.fst _)
    (TopologicalSpace.induced Prod.snd _)).trans <|
    continuous_induced_rng.and continuous_induced_rng

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst X Y) :=
  (continuous_prod_mk.1 continuous_id).1

/-- Postcomposing `f` with `Prod.fst` is continuous -/
@[fun_prop]
theorem Continuous.fst {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).1 :=
  continuous_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous -/
theorem Continuous.fst' {f : X → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.fst :=
  hf.comp continuous_fst

theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
  continuous_fst.continuousAt

/-- Postcomposing `f` with `Prod.fst` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.fst {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).1) x :=
  continuousAt_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : X → Z} {x : X} {y : Y} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X × Y => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst

/-- Precomposing `f` with `Prod.fst` is continuous at `x : X × Y` -/
theorem ContinuousAt.fst'' {f : X → Z} {x : X × Y} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : X × Y => f x.fst) x :=
  hf.comp continuousAt_fst

theorem Filter.Tendsto.fst_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).1) l (𝓝 <| p.1) :=
  continuousAt_fst.tendsto.comp h

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd X Y) :=
  (continuous_prod_mk.1 continuous_id).2

/-- Postcomposing `f` with `Prod.snd` is continuous -/
@[fun_prop]
theorem Continuous.snd {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).2 :=
  continuous_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous -/
theorem Continuous.snd' {f : Y → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.snd :=
  hf.comp continuous_snd

theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
  continuous_snd.continuousAt

/-- Postcomposing `f` with `Prod.snd` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.snd {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).2) x :=
  continuousAt_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : Y → Z} {x : X} {y : Y} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : X × Y => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd

/-- Precomposing `f` with `Prod.snd` is continuous at `x : X × Y` -/
theorem ContinuousAt.snd'' {f : Y → Z} {x : X × Y} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : X × Y => f x.snd) x :=
  hf.comp continuousAt_snd

theorem Filter.Tendsto.snd_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).2) l (𝓝 <| p.2) :=
  continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]
theorem Continuous.prod_mk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_prod_mk.2 ⟨hf, hg⟩

@[continuity]
theorem Continuous.Prod.mk (x : X) : Continuous fun y : Y => (x, y) :=
  continuous_const.prod_mk continuous_id

@[continuity]
theorem Continuous.Prod.mk_left (y : Y) : Continuous fun x : X => (x, y) :=
  continuous_id.prod_mk continuous_const

/-- If `f x y` is continuous in `x` for all `y ∈ s`,
then the set of `x` such that `f x` maps `s` to `t` is closed. -/
lemma IsClosed.setOf_mapsTo {α : Type*} {f : X → α → Z} {s : Set α} {t : Set Z} (ht : IsClosed t)
    (hf : ∀ a ∈ s, Continuous (f · a)) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, setOf_forall] using isClosed_biInter fun y hy ↦ ht.preimage (hf y hy)

theorem Continuous.comp₂ {g : X × Y → Z} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) : Continuous fun w => g (e w, f w) :=
  hg.comp <| he.prod_mk hf

theorem Continuous.comp₃ {g : X × Y × Z → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) :
    Continuous fun w => g (e w, f w, k w) :=
  hg.comp₂ he <| hf.prod_mk hk

theorem Continuous.comp₄ {g : X × Y × Z × ζ → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) {l : W → ζ}
    (hl : Continuous l) : Continuous fun w => g (e w, f w, k w, l w) :=
  hg.comp₃ he hf <| hk.prod_mk hl

@[continuity]
theorem Continuous.prodMap {f : Z → X} {g : W → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Prod.map f g) :=
  hf.fst'.prod_mk hg.snd'

@[deprecated (since := "2024-10-05")] alias Continuous.prod_map := Continuous.prodMap

/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta1; haveI := tb1; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta2; haveI := tb2; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_sInf_dom` for binary functions -/
theorem continuous_sInf_dom₂ {X Y Z} {f : X → Y → Z} {tas : Set (TopologicalSpace X)}
    {tbs : Set (TopologicalSpace Y)} {tX : TopologicalSpace X} {tY : TopologicalSpace Y}
    {tc : TopologicalSpace Z} (hX : tX ∈ tas) (hY : tY ∈ tbs)
    (hf : Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id

theorem Filter.Eventually.prod_inl_nhds {p : X → Prop} {x : X} (h : ∀ᶠ x in 𝓝 x, p x) (y : Y) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).1 :=
  continuousAt_fst h

theorem Filter.Eventually.prod_inr_nhds {p : Y → Prop} {y : Y} (h : ∀ᶠ x in 𝓝 y, p x) (x : X) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).2 :=
  continuousAt_snd h

theorem Filter.Eventually.prod_mk_nhds {px : X → Prop} {x} (hx : ∀ᶠ x in 𝓝 x, px x) {py : Y → Prop}
    {y} (hy : ∀ᶠ y in 𝓝 y, py y) : ∀ᶠ p in 𝓝 (x, y), px (p : X × Y).1 ∧ py p.2 :=
  (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

theorem continuous_swap : Continuous (Prod.swap : X × Y → Y × X) :=
  continuous_snd.prod_mk continuous_fst

lemma isClosedMap_swap : IsClosedMap (Prod.swap : X × Y → Y × X) := fun s hs ↦ by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

theorem isOpenMap_swap : IsOpenMap (Prod.swap : X × Y → Y × X) := by
  intro s hs
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

theorem Continuous.uncurry_left {f : X → Y → Z} (x : X) (h : Continuous (uncurry f)) :
    Continuous (f x) :=
  h.comp (Continuous.Prod.mk _)

theorem Continuous.uncurry_right {f : X → Y → Z} (y : Y) (h : Continuous (uncurry f)) :
    Continuous fun a => f a y :=
  h.comp (Continuous.Prod.mk_left _)


theorem continuous_curry {g : X × Y → Z} (x : X) (h : Continuous g) : Continuous (curry g x) :=
  Continuous.uncurry_left x h

theorem IsOpen.curry_left {s : Set (X × Y)} (hs : IsOpen s) (x : X) : IsOpen ((x, ·) ⁻¹' s) :=
  hs.preimage (Continuous.Prod.mk _)

theorem IsOpen.curry_right {s : Set (X × Y)} (hs : IsOpen s) (y : Y) : IsOpen ((·, y) ⁻¹' s) :=
  (hs.preimage continuous_swap).curry_left y

theorem IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Lean fails to find `t₁` and `t₂` by unification
theorem nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y := by
  rw [prod_eq_inf, instTopologicalSpaceProd, nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _), nhds_induced, nhds_induced]

theorem nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) :
    𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y := by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]

instance Prod.instNeBotNhdsWithinIio [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[<] x.1).NeBot] [hx₂ : (𝓝[<] x.2).NeBot] : (𝓝[<] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
  exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ ↦ Prod.lt_iff.2 <| .inl ⟨h₁, h₂.le⟩

instance Prod.instNeBotNhdsWithinIoi [Preorder X] [Preorder Y] {x : X × Y}
    [(𝓝[>] x.1).NeBot] [(𝓝[>] x.2).NeBot] : (𝓝[>] x).NeBot :=
  Prod.instNeBotNhdsWithinIio (X := Xᵒᵈ) (Y := Yᵒᵈ)
    (x := (OrderDual.toDual x.1, OrderDual.toDual x.2))

theorem mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u ∈ 𝓝 x, ∃ v ∈ 𝓝 y, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]

theorem mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y} :
    s ∈ 𝓝[tx ×ˢ ty] (x, y) ↔ ∃ u ∈ 𝓝[tx] x, ∃ v ∈ 𝓝[ty] y, u ×ˢ v ⊆ s := by
  rw [nhdsWithin_prod_eq, mem_prod_iff]

theorem Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX → Prop} {py : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis px sx)
    (hy : (𝓝 y).HasBasis py sy) :
    (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2 := by
  rw [nhds_prod_eq]
  exact hx.prod hy

theorem Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX → Prop} {pY : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX sx)
    (hy : (𝓝 p.2).HasBasis pY sy) :
    (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧ pY i.2) fun i => sx i.1 ×ˢ sy i.2 :=
  hx.prod_nhds hy

theorem MapClusterPt.curry_prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la.curry lb) (.map f g) := by
  rw [mapClusterPt_iff] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx ↦ (hg t ht).mono fun y hy ↦ ⟨hx, hy⟩

theorem MapClusterPt.prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la ×ˢ lb) (.map f g) :=
  (hf.curry_prodMap hg).mono <| map_mono curry_le_prod

theorem mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧ u ×ˢ v ⊆ s :=
  ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans <| by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

theorem Prod.tendsto_iff {X} (seq : X → Y × Z) {f : Filter X} (p : Y × Z) :
    Tendsto seq f (𝓝 p) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd) := by
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']

instance [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq, nhds_discrete X, nhds_discrete Y, prod_pure_pure]

theorem prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} :
    s ×ˢ t ∈ 𝓝 (x, y) ↔ s ∈ 𝓝 x ∧ t ∈ 𝓝 y := by rw [nhds_prod_eq, prod_mem_prod_iff]

theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s ∈ 𝓝 x) (hy : t ∈ 𝓝 y) :
    s ×ˢ t ∈ 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩

theorem isOpen_setOf_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_setOf_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩

theorem Filter.Eventually.prod_nhds {p : X → Prop} {q : Y → Prop} {x : X} {y : Y}
    (hx : ∀ᶠ x in 𝓝 x, p x) (hy : ∀ᶠ y in 𝓝 y, q y) : ∀ᶠ z : X × Y in 𝓝 (x, y), p z.1 ∧ q z.2 :=
  prod_mem_nhds hx hy

theorem Filter.EventuallyEq.prodMap_nhds {α β : Type*} {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) (hg : g₁ =ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ =ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prod_map hg

theorem Filter.EventuallyLE.prodMap_nhds {α β : Type*} [LE α] [LE β] {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ ≤ᶠ[𝓝 x] f₂) (hg : g₁ ≤ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ ≤ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prod_map hg

theorem nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq]; rfl

theorem Filter.Tendsto.prod_mk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y}
    (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) :
    Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y)) := by
  rw [nhds_prod_eq]; exact Filter.Tendsto.prod_mk hx hy

theorem Filter.Tendsto.prodMap_nhds {x : X} {y : Y} {z : Z} {w : W} {f : X → Y} {g : Z → W}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Tendsto g (𝓝 z) (𝓝 w)) :
    Tendsto (Prod.map f g) (𝓝 (x, z)) (𝓝 (y, w)) := by
  rw [nhds_prod_eq, nhds_prod_eq]
  exact hf.prod_map hg

theorem Filter.Eventually.curry_nhds {p : X × Y → Prop} {x : X} {y : Y}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]
theorem ContinuousAt.prod {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg

theorem ContinuousAt.prodMap {f : X → Z} {g : Y → W} {p : X × Y} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (Prod.map f g) p :=
  hf.fst''.prod hg.snd''

@[deprecated (since := "2024-10-05")] alias ContinuousAt.prod_map := ContinuousAt.prodMap

/-- A version of `ContinuousAt.prodMap` that avoids `Prod.fst`/`Prod.snd`
by assuming that the point is `(x, y)`. -/
theorem ContinuousAt.prodMap' {f : X → Z} {g : Y → W} {x : X} {y : Y} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (Prod.map f g) (x, y) :=
  hf.prodMap hg

@[deprecated (since := "2024-10-05")] alias ContinuousAt.prod_map' := ContinuousAt.prodMap'

theorem ContinuousAt.comp₂ {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X}
    (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh : ContinuousAt h x) :
    ContinuousAt (fun x ↦ f (g x, h x)) x :=
  ContinuousAt.comp hf (hg.prod hh)

theorem ContinuousAt.comp₂_of_eq {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X} {y : Y × Z}
    (hf : ContinuousAt f y) (hg : ContinuousAt g x) (hh : ContinuousAt h x) (e : (g x, h x) = y) :
    ContinuousAt (fun x ↦ f (g x, h x)) x := by
  rw [← e] at hf
  exact hf.comp₂ hg hh

/-- Continuous functions on products are continuous in their first argument -/
theorem Continuous.curry_left {f : X × Y → Z} (hf : Continuous f) {y : Y} :
    Continuous fun x ↦ f (x, y) :=
  hf.comp (continuous_id.prod_mk continuous_const)
alias Continuous.along_fst := Continuous.curry_left

/-- Continuous functions on products are continuous in their second argument -/
theorem Continuous.curry_right {f : X × Y → Z} (hf : Continuous f) {x : X} :
    Continuous fun y ↦ f (x, y) :=
  hf.comp (continuous_const.prod_mk continuous_id)
alias Continuous.along_snd := Continuous.curry_right

-- todo: prove a version of `generateFrom_union` with `image2 (∩) s t` in the LHS and use it here
theorem prod_generateFrom_generateFrom_eq {X Y : Type*} {s : Set (Set X)} {t : Set (Set Y)}
    (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
    @instTopologicalSpaceProd X Y (generateFrom s) (generateFrom t) =
      generateFrom (image2 (·  ×ˢ ·) s t) :=
  let G := generateFrom (image2  (·  ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun u hu =>
          have : ⋃ v ∈ t, u ×ˢ v = Prod.fst ⁻¹' u := by
            simp_rw [← prod_iUnion, ← sUnion_eq_biUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact
              isOpen_iUnion fun v =>
                isOpen_iUnion fun hv => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun v hv =>
          have : ⋃ u ∈ s, u ×ˢ v = Prod.snd ⁻¹' v := by
            simp_rw [← iUnion_prod_const, ← sUnion_eq_biUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact
              isOpen_iUnion fun u =>
                isOpen_iUnion fun hu => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩))

-- todo: use the previous lemma?
theorem prod_eq_generateFrom :
    instTopologicalSpaceProd =
      generateFrom { g | ∃ (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨t, univ, by simpa [Set.prod_eq] using ht⟩)
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨univ, t, by simpa [Set.prod_eq] using ht⟩))

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: align with `mem_nhds_prod_iff'`
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  isOpen_iff_mem_nhds.trans <| by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced {X Z} (f : X → Y) (g : Z → W) :
    @instTopologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instTopologicalSpaceProd := by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (X × X)} {x : X} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

/-- `Prod.fst` maps neighborhood of `x : X × Y` within the section `Prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
theorem map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuousAt_fst <| (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

/-- `Prod.snd` maps neighborhood of `x : X × Y` within the section `Prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
theorem map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuousAt_snd <| (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem isOpen_prod_iff' {s : Set X} {t : Set Y} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
      · simpa only [snd_image_prod st.1 t] using isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false] at H
      exact H.1.prod H.2

theorem isQuotientMap_fst [Nonempty Y] : IsQuotientMap (Prod.fst : X × Y → X) :=
  isOpenMap_fst.isQuotientMap continuous_fst Prod.fst_surjective

@[deprecated (since := "2024-10-22")]
alias quotientMap_fst := isQuotientMap_fst

theorem isQuotientMap_snd [Nonempty X] : IsQuotientMap (Prod.snd : X × Y → Y) :=
  isOpenMap_snd.isQuotientMap continuous_snd Prod.snd_surjective

@[deprecated (since := "2024-10-22")]
alias quotientMap_snd := isQuotientMap_snd

theorem closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]

theorem interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

theorem frontier_prod_eq (s : Set X) (t : Set Y) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]

@[simp]
theorem frontier_prod_univ_eq (s : Set X) :
    frontier (s ×ˢ (univ : Set Y)) = frontier s ×ˢ univ := by
  simp [frontier_prod_eq]

@[simp]
theorem frontier_univ_prod_eq (s : Set Y) :
    frontier ((univ : Set X) ×ˢ s) = univ ×ˢ frontier s := by
  simp [frontier_prod_eq]

theorem map_mem_closure₂ {f : X → Y → Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf : Continuous (uncurry f)) (hx : x ∈ closure s) (hy : y ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f x y ∈ closure u :=
  have H₁ : (x, y) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁

theorem IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_isClosed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

/-- If `f` and `g` are maps with dense range, then `Prod.map f g` has dense range. -/
theorem DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι → Y} {g : κ → Z} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using hf.prod hg

@[deprecated (since := "2024-10-05")] alias DenseRange.prod_map := DenseRange.prodMap

lemma Topology.IsInducing.prodMap {f : X → Y} {g : Z → W} (hf : IsInducing f) (hg : IsInducing g) :
    IsInducing (Prod.map f g) :=
  isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[deprecated (since := "2024-10-28")] alias Inducing.prodMap := IsInducing.prodMap

@[deprecated (since := "2024-10-05")] alias Inducing.prod_map := IsInducing.prodMap

@[simp]
lemma Topology.isInducing_const_prod {x : X} {f : Y → Z} :
    IsInducing (fun x' => (x, f x')) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[deprecated (since := "2024-10-28")] alias inducing_const_prod := isInducing_const_prod

@[simp]
lemma Topology.isInducing_prod_const {y : Y} {f : X → Z} :
    IsInducing (fun x => (f x, y)) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]

@[deprecated (since := "2024-10-28")] alias inducing_prod_const := isInducing_prod_const

lemma Topology.IsEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Prod.map f g) where
  toIsInducing := hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective

@[deprecated (since := "2024-10-08")] alias Embedding.prodMap := Topology.IsEmbedding.prodMap
@[deprecated (since := "2024-10-05")] alias Embedding.prod_map := Topology.IsEmbedding.prodMap

protected theorem IsOpenMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Prod.map f g) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

@[deprecated (since := "2024-10-05")] alias IsOpenMap.prod := IsOpenMap.prodMap

protected lemma Topology.IsOpenEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) : IsOpenEmbedding (Prod.map f g) :=
  .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.prodMap := IsOpenEmbedding.prodMap

@[deprecated (since := "2024-10-05")] alias IsOpenEmbedding.prod := IsOpenEmbedding.prodMap

lemma isEmbedding_graph {f : X → Y} (hf : Continuous f) : IsEmbedding fun x => (x, f x) :=
  .of_comp (continuous_id.prod_mk hf) continuous_fst .id

@[deprecated (since := "2024-10-26")]
alias embedding_graph := isEmbedding_graph

lemma isEmbedding_prodMk (x : X) : IsEmbedding (Prod.mk x : Y → X × Y) :=
  .of_comp (Continuous.Prod.mk x) continuous_snd .id

@[deprecated (since := "2024-10-26")]
alias embedding_prod_mk := isEmbedding_prodMk

theorem IsOpenQuotientMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenQuotientMap f)
    (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (Prod.map f g) :=
  ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

end Prod

section Bool

lemma continuous_bool_rng [TopologicalSpace X] {f : X → Bool} (b : Bool) :
    Continuous f ↔ IsClopen (f ⁻¹' {b}) := by
  rw [continuous_discrete_rng, Bool.forall_bool' b, IsClopen, ← isOpen_compl_iff, ← preimage_compl,
    Bool.compl_singleton, and_comm]

end Bool

section Sum

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

theorem continuous_sum_dom {f : X ⊕ Y → Z} :
    Continuous f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr) :=
  (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

theorem continuous_sumElim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom

@[deprecated (since := "2025-02-20")] alias continuous_sum_elim := continuous_sumElim

@[continuity, fun_prop]
theorem Continuous.sumElim {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias Continuous.sum_elim := Continuous.sumElim

@[continuity, fun_prop]
theorem continuous_isLeft : Continuous (isLeft : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_isRight : Continuous (isRight : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩

@[continuity, fun_prop]
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩

@[fun_prop, continuity]
lemma continuous_sum_swap : Continuous (@Sum.swap X Y) :=
  Continuous.sumElim continuous_inr continuous_inl

theorem isOpen_sum_iff {s : Set (X ⊕ Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

theorem isClosed_sum_iff {s : Set (X ⊕ Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

theorem isClosedMap_inl : IsClosedMap (@inl X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isClosedMap_inr : IsClosedMap (@inr X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

protected lemma Topology.IsOpenEmbedding.inl : IsOpenEmbedding (@inl X Y) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inl := IsOpenEmbedding.inl

@[deprecated (since := "2024-10-18")]
alias openEmbedding_inl := IsOpenEmbedding.inl

protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
  .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inr := IsOpenEmbedding.inr

@[deprecated (since := "2024-10-18")]
alias openEmbedding_inr := IsOpenEmbedding.inr

protected lemma Topology.IsEmbedding.inl : IsEmbedding (@inl X Y) := IsOpenEmbedding.inl.1
protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1

@[deprecated (since := "2024-10-26")]
alias embedding_inr := IsEmbedding.inr

lemma isOpen_range_inl : IsOpen (range (inl : X → X ⊕ Y)) := IsOpenEmbedding.inl.2
lemma isOpen_range_inr : IsOpen (range (inr : Y → X ⊕ Y)) := IsOpenEmbedding.inr.2

theorem isClosed_range_inl : IsClosed (range (inl : X → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr

theorem isClosed_range_inr : IsClosed (range (inr : Y → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl

theorem Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X → X ⊕ Y) :=
  ⟨.inl, isClosed_range_inl⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inl := IsClosedEmbedding.inl

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_inl := IsClosedEmbedding.inl

theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y → X ⊕ Y) :=
  ⟨.inr, isClosed_range_inr⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inr := IsClosedEmbedding.inr

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_inr := IsClosedEmbedding.inr

theorem nhds_inl (x : X) : 𝓝 (inl x : X ⊕ Y) = map inl (𝓝 x) :=
  (IsOpenEmbedding.inl.map_nhds_eq _).symm

theorem nhds_inr (y : Y) : 𝓝 (inr y : X ⊕ Y) = map inr (𝓝 y) :=
  (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]
theorem continuous_sumMap {f : X → Y} {g : Z → W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sumElim.trans <|
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[deprecated (since := "2025-02-21")] alias continuous_sum_map := continuous_sumMap

@[continuity, fun_prop]
theorem Continuous.sumMap {f : X → Y} {g : Z → W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sumMap.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-21")] alias Continuous.sum_map := Continuous.sumMap

theorem isOpenMap_sum {f : X ⊕ Y → Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

theorem IsOpenMap.sumMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.map f g) :=
  isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]
theorem isOpenMap_sumElim {f : X → Z} {g : Y → Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

@[deprecated (since := "2025-02-20")] alias isOpenMap_sum_elim := isOpenMap_sumElim

theorem IsOpenMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias IsOpenMap.sum_elim := IsOpenMap.sumElim

lemma IsOpenEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) :
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

theorem isClosedMap_sum {f : X ⊕ Y → Z} :
    IsClosedMap f ↔ (IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b) := by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

theorem IsClosedMap.sumMap {f : X → Y} {g : Z → W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.map f g) :=
  isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]
theorem isClosedMap_sumElim {f : X → Z} {g : Y → Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

theorem IsClosedMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sumElim.2 ⟨hf, hg⟩

lemma IsClosedEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

end Sum

section Subtype

variable [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop}

lemma Topology.IsInducing.subtypeVal {t : Set Y} : IsInducing ((↑) : t → Y) := ⟨rfl⟩

@[deprecated (since := "2024-10-28")] alias inducing_subtype_val := IsInducing.subtypeVal

lemma Topology.IsInducing.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (h : IsInducing (t.codRestrict f ht)) : IsInducing f := subtypeVal.comp h

@[deprecated (since := "2024-10-28")] alias Inducing.of_codRestrict := IsInducing.of_codRestrict

lemma Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, Subtype.coe_injective⟩

@[deprecated (since := "2024-10-26")] alias embedding_subtype_val := IsEmbedding.subtypeVal

theorem Topology.IsClosedEmbedding.subtypeVal (h : IsClosed {a | p a}) :
    IsClosedEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_subtype_val := IsClosedEmbedding.subtypeVal

@[continuity, fun_prop]
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom

theorem Continuous.subtype_val {f : Y → Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : X) :=
  continuous_subtype_val.comp hf

theorem IsOpen.isOpenEmbedding_subtypeVal {s : Set X} (hs : IsOpen s) :
    IsOpenEmbedding ((↑) : s → X) :=
  ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩

@[deprecated (since := "2024-10-18")]
alias IsOpen.openEmbedding_subtype_val := IsOpen.isOpenEmbedding_subtypeVal

theorem IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) : s → X) :=
  hs.isOpenEmbedding_subtypeVal.isOpenMap

theorem IsOpenMap.restrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
    IsOpenMap (s.restrict f) :=
  hf.comp hs.isOpenMap_subtype_val

lemma IsClosed.isClosedEmbedding_subtypeVal {s : Set X} (hs : IsClosed s) :
    IsClosedEmbedding ((↑) : s → X) := .subtypeVal hs

@[deprecated (since := "2024-10-20")]
alias IsClosed.closedEmbedding_subtype_val := IsClosed.isClosedEmbedding_subtypeVal

theorem IsClosed.isClosedMap_subtype_val {s : Set X} (hs : IsClosed s) :
    IsClosedMap ((↑) : s → X) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap

@[continuity, fun_prop]
theorem Continuous.subtype_mk {f : Y → X} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
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
    ∀ {x : Subtype p}, Tendsto f l (𝓝 x) ↔ Tendsto (fun x => (f x : X)) l (𝓝 (x : X))
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

theorem Topology.IsInducing.codRestrict {e : X → Y} (he : IsInducing e) {s : Set Y}
    (hs : ∀ x, e x ∈ s) : IsInducing (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

@[deprecated (since := "2024-10-28")] alias Inducing.codRestrict := IsInducing.codRestrict

protected lemma Topology.IsEmbedding.codRestrict {e : X → Y} (he : IsEmbedding e) (s : Set Y)
    (hs : ∀ x, e x ∈ s) : IsEmbedding (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

@[deprecated (since := "2024-10-26")]
alias Embedding.codRestrict := IsEmbedding.codRestrict

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

@[deprecated (since := "2024-10-26")]
alias embedding_inclusion := IsEmbedding.inclusion

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

@[deprecated (since := "2024-10-22")]
alias QuotientMap.restrictPreimage_isOpen := IsQuotientMap.restrictPreimage_isOpen

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

@[deprecated (since := "2024-10-22")]
alias quotientMap_quot_mk := isQuotientMap_quot_mk

@[continuity, fun_prop]
theorem continuous_quot_mk : Continuous (@Quot.mk X r) :=
  continuous_coinduced_rng

@[continuity, fun_prop]
theorem continuous_quot_lift {f : X → Y} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → Y) :=
  continuous_coinduced_dom.2 h

theorem isQuotientMap_quotient_mk' : IsQuotientMap (@Quotient.mk' X s) :=
  isQuotientMap_quot_mk

@[deprecated (since := "2024-10-22")]
alias quotientMap_quotient_mk' := isQuotientMap_quotient_mk'

theorem continuous_quotient_mk' : Continuous (@Quotient.mk' X s) :=
  continuous_coinduced_rng

theorem Continuous.quotient_lift {f : X → Y} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → Y) :=
  continuous_coinduced_dom.2 h

theorem Continuous.quotient_liftOn' {f : X → Y} (h : Continuous f)
    (hs : ∀ a b, s a b → f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s → Y) :=
  h.quotient_lift hs

@[continuity, fun_prop]
theorem Continuous.quotient_map' {t : Setoid Y} {f : X → Y} (hf : Continuous f)
    (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _

end Quotient

section Pi

variable {ι : Type*} {π : ι → Type*} {κ : Type*} [TopologicalSpace X]
  [T : ∀ i, TopologicalSpace (π i)] {f : X → ∀ i : ι, π i}

theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a => f a i := by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]
theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h

@[continuity, fun_prop]
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_iInf_dom continuous_induced_dom

@[continuity]
theorem continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)

theorem continuousAt_apply (i : ι) (x : ∀ i, π i) : ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).continuousAt

theorem Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y → ∀ i, π i} {x : ∀ i, π i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).tendsto.comp h

@[fun_prop]
protected theorem Continuous.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, π i → Y i} (hf : ∀ i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i ↦ (hf i).comp (continuous_apply i)

theorem nhds_pi {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_iInf, nhds_induced, Filter.pi]

protected theorem IsOpenMap.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f : ∀ i, π i → Y i}
    (hfo : ∀ i, IsOpenMap (f i)) (hsurj : ∀ᶠ i in cofinite, Surjective (f i)) :
    IsOpenMap (Pi.map f) := by
  refine IsOpenMap.of_nhds_le fun x ↦ ?_
  rw [nhds_pi, nhds_pi, map_piMap_pi hsurj]
  exact Filter.pi_mono fun i ↦ (hfo i).nhds_le _

protected theorem IsOpenQuotientMap.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, π i → Y i} (hf : ∀ i, IsOpenQuotientMap (f i)) : IsOpenQuotientMap (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2, .piMap (fun i ↦ (hf i).3) <|
    .of_forall fun i ↦ (hf i).1⟩

theorem tendsto_pi_nhds {f : Y → ∀ i, π i} {g : ∀ i, π i} {u : Filter Y} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]

theorem continuousAt_pi {f : X → ∀ i, π i} {x : X} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds

@[fun_prop]
theorem continuousAt_pi' {f : X → ∀ i, π i} {x : X} (hf : ∀ i, ContinuousAt (fun y => f y i) x) :
    ContinuousAt f x :=
  continuousAt_pi.2 hf

@[fun_prop]
protected theorem ContinuousAt.piMap {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, π i → Y i} {x : ∀ i, π i} (hf : ∀ i, ContinuousAt (f i) (x i)) :
    ContinuousAt (Pi.map f) x :=
  continuousAt_pi.2 fun i ↦ (hf i).comp (continuousAt_apply i x)

theorem Pi.continuous_precomp' {ι' : Type*} (φ : ι' → ι) :
    Continuous (fun (f : (∀ i, π i)) (j : ι') ↦ f (φ j)) :=
  continuous_pi fun j ↦ continuous_apply (φ j)

theorem Pi.continuous_precomp {ι' : Type*} (φ : ι' → ι) :
    Continuous (· ∘ φ : (ι → X) → (ι' → X)) :=
  Pi.continuous_precomp' φ

theorem Pi.continuous_postcomp' {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {g : ∀ i, π i → X i} (hg : ∀ i, Continuous (g i)) :
    Continuous (fun (f : (∀ i, π i)) (i : ι) ↦ g i (f i)) :=
  continuous_pi fun i ↦ (hg i).comp <| continuous_apply i

theorem Pi.continuous_postcomp [TopologicalSpace Y] {g : X → Y} (hg : Continuous g) :
    Continuous (g ∘ · : (ι → X) → (ι → Y)) :=
  Pi.continuous_postcomp' fun _ ↦ hg

lemma Pi.induced_precomp' {ι' : Type*} (φ : ι' → ι) :
    induced (fun (f : (∀ i, π i)) (j : ι') ↦ f (φ j)) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) (T (φ i')) := by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]

lemma Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' → ι) :
    induced (· ∘ φ) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y› :=
  induced_precomp' φ

@[continuity, fun_prop]
lemma Pi.continuous_restrict (S : Set ι) :
    Continuous (S.restrict : (∀ i : ι, π i) → (∀ i : S, π i)) :=
  Pi.continuous_precomp' ((↑) : S → ι)

@[continuity, fun_prop]
lemma Pi.continuous_restrict₂ {s t : Set ι} (hst : s ⊆ t) : Continuous (restrict₂ (π := π) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

@[continuity, fun_prop]
theorem Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π := π)) :=
  continuous_pi fun _ ↦ continuous_apply _

@[continuity, fun_prop]
theorem Finset.continuous_restrict₂ {s t : Finset ι} (hst : s ⊆ t) :
    Continuous (Finset.restrict₂ (π := π) hst) :=
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
  simp (config := { unfoldPartialApp := true }) [← iInf_subtype'', ← induced_precomp' ((↑) : S → ι),
    restrict]

lemma Pi.induced_restrict_sUnion (𝔖 : Set (Set ι)) :
    induced (⋃₀ 𝔖).restrict (Pi.topologicalSpace (Y := fun i : (⋃₀ 𝔖) ↦ π i)) =
    ⨅ S ∈ 𝔖, induced S.restrict Pi.topologicalSpace := by
  simp_rw [Pi.induced_restrict, iInf_sUnion]

theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter Y} {f : Y → ∀ i, π i} {x : ∀ i, π i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : Y → π i} {xi : π i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j => by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

theorem ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X → π i}
    (hg : ContinuousAt g x) : ContinuousAt (fun a => update (f a) i (g a)) x :=
  hf.tendsto.update i hg

theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X → π i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt

/-- `Function.update f i x` is continuous in `(f, x)`. -/
@[continuity, fun_prop]
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, π j) × π i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

/-- `Pi.mulSingle i x` is continuous in `x`. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore @[continuity]
@[to_additive "`Pi.single i x` is continuous in `x`."]
theorem continuous_mulSingle [∀ i, One (π i)] [DecidableEq ι] (i : ι) :
    Continuous fun x => (Pi.mulSingle i x : ∀ i, π i) :=
  continuous_const.update _ continuous_id

section Fin
variable {n : ℕ} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]

theorem Filter.Tendsto.finCons
    {f : Y → π 0} {g : Y → ∀ j : Fin n, π j.succ} {l : Filter Y} {x : π 0} {y : ∀ j, π (Fin.succ j)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.cons (f a) (g a)) l (𝓝 <| Fin.cons x y) :=
  tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

theorem ContinuousAt.finCons {f : X → π 0} {g : X → ∀ j : Fin n, π (Fin.succ j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.cons (f a) (g a)) x :=
  hf.tendsto.finCons hg

theorem Continuous.finCons {f : X → π 0} {g : X → ∀ j : Fin n, π (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt

theorem Filter.Tendsto.matrixVecCons
    {f : Y → Z} {g : Y → Fin n → Z} {l : Filter Y} {x : Z} {y : Fin n → Z}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y) :=
  hf.finCons hg

theorem ContinuousAt.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Matrix.vecCons (f a) (g a)) x :=
  hf.finCons hg

theorem Continuous.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => Matrix.vecCons (f a) (g a) :=
  hf.finCons hg

theorem Filter.Tendsto.finSnoc
    {f : Y → ∀ j : Fin n, π j.castSucc} {g : Y → π (Fin.last _)}
    {l : Filter Y} {x : ∀ j, π (Fin.castSucc j)} {y : π (Fin.last _)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y) :=
  tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

theorem ContinuousAt.finSnoc {f : X → ∀ j : Fin n, π j.castSucc} {g : X → π (Fin.last _)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.snoc (f a) (g a)) x :=
  hf.tendsto.finSnoc hg

theorem Continuous.finSnoc {f : X → ∀ j : Fin n, π j.castSucc} {g : X → π (Fin.last _)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.snoc (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt

theorem Filter.Tendsto.finInsertNth
    (i : Fin (n + 1)) {f : Y → π i} {g : Y → ∀ j : Fin n, π (i.succAbove j)} {l : Filter Y}
    {x : π i} {y : ∀ j, π (i.succAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[deprecated (since := "2025-01-02")]
alias Filter.Tendsto.fin_insertNth := Filter.Tendsto.finInsertNth

theorem ContinuousAt.finInsertNth
    (i : Fin (n + 1)) {f : X → π i} {g : X → ∀ j : Fin n, π (i.succAbove j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) x :=
  hf.tendsto.finInsertNth i hg

@[deprecated (since := "2025-01-02")]
alias ContinuousAt.fin_insertNth := ContinuousAt.finInsertNth

theorem Continuous.finInsertNth
    (i : Fin (n + 1)) {f : X → π i} {g : X → ∀ j : Fin n, π (i.succAbove j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt

@[deprecated (since := "2025-01-02")]
alias Continuous.fin_insertNth := Continuous.finInsertNth

end Fin

theorem isOpen_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

theorem isOpen_pi_iff {s : Set (∀ a, π a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ (I : Finset ι) (u : ∀ a, Set (π a)),
        (∀ a, a ∈ I → IsOpen (u a) ∧ f a ∈ u a) ∧ (I : Set ι).pi u ⊆ s := by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine ⟨I, fun a => eval a '' (I : Set ι).pi fun a => (h1 a).choose, fun i hi => ?_, ?_⟩
    · simp_rw [eval_image_pi (Finset.mem_coe.mpr hi)
          (pi_nonempty_iff.mpr fun i => ⟨_, fun _ => (h1 i).choose_spec.2.2⟩)]
      exact (h1 i).choose_spec.2
    · exact Subset.trans
        (pi_mono fun i hi => (eval_image_pi_subset hi).trans (h1 i).choose_spec.1) h2
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    classical
    refine ⟨I, fun a => ite (a ∈ I) (t a) univ, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ I
      · use t i
        simp_rw [if_pos hi]
        exact ⟨Subset.rfl, (h1 i) hi⟩
      · use univ
        simp_rw [if_neg hi]
        exact ⟨Subset.rfl, isOpen_univ, mem_univ _⟩
    · rw [← univ_pi_ite]
      simp only [← ite_and, ← Finset.mem_coe, and_self_iff, univ_pi_ite, h2]

theorem isOpen_pi_iff' [Finite ι] {s : Set (∀ a, π a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ u : ∀ a, Set (π a), (∀ a, IsOpen (u a) ∧ f a ∈ u a) ∧ univ.pi u ⊆ s := by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine
      ⟨fun i => (h1 i).choose,
        ⟨fun i => (h1 i).choose_spec.2,
          (pi_mono fun i _ => (h1 i).choose_spec.1).trans (Subset.trans ?_ h2)⟩⟩
    rw [← pi_inter_compl (I : Set ι)]
    exact inter_subset_left
  · exact fun ⟨u, ⟨h1, _⟩⟩ =>
      ⟨Finset.univ, u, ⟨fun i => ⟨u i, ⟨rfl.subset, h1 i⟩⟩, by rwa [Finset.coe_univ]⟩⟩

theorem isClosed_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (π i)} (a : ∀ i, π i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi

theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)

theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} (a : ∀ i, π i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]

theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} :
    interior (pi I s) = I.pi fun i => interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, π a)} {x : ∀ a, π a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

theorem pi_generateFrom_eq {π : ι → Type*} {g : ∀ a, Set (Set (π a))} :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (π a)) (i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    letI := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · classical
    refine le_iInf fun i => coinduced_le_iff_le_induced.1 <| le_generateFrom fun s hs => ?_
    refine GenerateOpen.basic _ ⟨update (fun i => univ) i s, {i}, ?_⟩
    simp [hs]

theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (π a)) (i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι π fun _ => generateFrom { s | IsOpen s } := by
    simp only [generateFrom_setOf_isOpen]
  _ = _ := pi_generateFrom_eq

theorem pi_generateFrom_eq_finite {π : ι → Type*} {g : ∀ a, Set (Set (π a))} [Finite ι]
    (hg : ∀ a, ⋃₀ g a = univ) :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (π a), (∀ a, s a ∈ g a) ∧ t = pi univ s } := by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    letI := generateFrom { t | ∃ s : ∀ a, Set (π a), (∀ a, s a ∈ g a) ∧ t = pi univ s }
    refine isOpen_iff_forall_mem_open.2 fun f hf => ?_
    choose c hcg hfc using fun a => sUnion_eq_univ_iff.1 (hg a) (f a)
    refine ⟨pi i t ∩ pi ((↑i)ᶜ : Set ι) c, inter_subset_left, ?_, ⟨hf, fun a _ => hfc a⟩⟩
    classical
    rw [← univ_pi_piecewise]
    refine GenerateOpen.basic _ ⟨_, fun a => ?_, rfl⟩
    by_cases a ∈ i <;> simp [*]

theorem induced_to_pi {X : Type*} (f : X → ∀ i, π i) :
    induced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance := by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_iInf_to_pi {X : Type*} (f : ∀ i, X → π i) :
    @IsInducing X (∀ i, π i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x :=
  letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

variable [Finite ι] [∀ i, DiscreteTopology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discreteTopology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})

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

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_sigmaMk := IsOpenEmbedding.sigmaMk

@[deprecated (since := "2024-10-18")]
alias openEmbedding_sigmaMk := IsOpenEmbedding.sigmaMk

lemma Topology.IsClosedEmbedding.sigmaMk {i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_sigmaMk := IsClosedEmbedding.sigmaMk

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_sigmaMk := IsClosedEmbedding.sigmaMk

lemma Topology.IsEmbedding.sigmaMk {i : ι} : IsEmbedding (@Sigma.mk ι σ i) :=
  IsClosedEmbedding.sigmaMk.1

@[deprecated (since := "2024-10-26")]
alias embedding_sigmaMk := IsEmbedding.sigmaMk

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
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
theorem continuous_sigma_iff {f : Sigma σ → X} :
    Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ := by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity, fun_prop]
theorem continuous_sigma {f : Sigma σ → X} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :
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

theorem isOpenMap_sigma {f : Sigma σ → X} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]

theorem isOpenMap_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  isOpenMap_sigma.trans <|
    forall_congr' fun i => (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm

lemma Topology.isInducing_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h₁ : Injective f₁) : IsInducing (Sigma.map f₁ f₂) ↔ ∀ i, IsInducing (f₂ i) := by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]

@[deprecated (since := "2024-10-28")] alias inducing_sigma_map := isInducing_sigmaMap

lemma Topology.isEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h : Injective f₁) : IsEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsEmbedding (f₂ i) := by
  simp only [isEmbedding_iff, Injective.sigma_map, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]

@[deprecated (since := "2024-10-26")]
alias embedding_sigma_map := isEmbedding_sigmaMap

lemma Topology.isOpenEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    IsOpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenEmbedding (f₂ i) := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_sigma_map := isOpenEmbedding_sigmaMap

@[deprecated (since := "2024-10-18")]
alias openEmbedding_sigma_map := isOpenEmbedding_sigmaMap

end Sigma

section ULift

theorem ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsOpen s ↔ IsOpen (ULift.up ⁻¹' s) := by
  rw [ULift.topologicalSpace, ← Equiv.ulift_apply, ← Equiv.ulift.coinduced_symm, ← isOpen_coinduced]

theorem ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsClosed s ↔ IsClosed (ULift.up ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_iff, preimage_compl]

@[continuity]
theorem continuous_uliftDown [TopologicalSpace X] : Continuous (ULift.down : ULift.{v, u} X → X) :=
  continuous_induced_dom

@[continuity]
theorem continuous_uliftUp [TopologicalSpace X] : Continuous (ULift.up : X → ULift.{v, u} X) :=
  continuous_induced_rng.2 continuous_id

@[deprecated (since := "2025-02-10")] alias continuous_uLift_down := continuous_uliftDown
@[deprecated (since := "2025-02-10")] alias continuous_uLift_up := continuous_uliftUp

@[continuity]
theorem continuous_uliftMap [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (ULift.map f : ULift.{u'} X → ULift.{v'} Y) := by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  continuity

lemma Topology.IsEmbedding.uliftDown [TopologicalSpace X] :
    IsEmbedding (ULift.down : ULift.{v, u} X → X) := ⟨⟨rfl⟩, ULift.down_injective⟩

@[deprecated (since := "2024-10-26")]
alias embedding_uLift_down := IsEmbedding.uliftDown

lemma Topology.IsClosedEmbedding.uliftDown [TopologicalSpace X] :
    IsClosedEmbedding (ULift.down : ULift.{v, u} X → X) :=
  ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩

@[deprecated (since := "2024-10-30")]
alias ULift.isClosedEmbedding_down := IsClosedEmbedding.uliftDown

@[deprecated (since := "2024-10-20")]
alias ULift.closedEmbedding_down := IsClosedEmbedding.uliftDown

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

set_option linter.style.longFile 2100
