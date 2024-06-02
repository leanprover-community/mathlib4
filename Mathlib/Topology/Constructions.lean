/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Maps
import Mathlib.Topology.NhdsSet

#align_import topology.constructions from "leanprover-community/mathlib"@"f7ebde7ee0d1505dfccac8644ae12371aa3c1c9f"

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

open scoped Classical
open Topology TopologicalSpace Set Filter Function

universe u v

variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*}

section Constructions

instance instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

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
#align Pi.topological_space Pi.topologicalSpace

instance ULift.topologicalSpace [t : TopologicalSpace X] : TopologicalSpace (ULift.{v, u} X) :=
  t.induced ULift.down
#align ulift.topological_space ULift.topologicalSpace

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
#align continuous_of_mul continuous_ofMul

theorem continuous_toMul : Continuous (toMul : Additive X → X) := continuous_id
#align continuous_to_mul continuous_toMul

theorem continuous_ofAdd : Continuous (ofAdd : X → Multiplicative X) := continuous_id
#align continuous_of_add continuous_ofAdd

theorem continuous_toAdd : Continuous (toAdd : Multiplicative X → X) := continuous_id
#align continuous_to_add continuous_toAdd

theorem isOpenMap_ofMul : IsOpenMap (ofMul : X → Additive X) := IsOpenMap.id
#align is_open_map_of_mul isOpenMap_ofMul

theorem isOpenMap_toMul : IsOpenMap (toMul : Additive X → X) := IsOpenMap.id
#align is_open_map_to_mul isOpenMap_toMul

theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : X → Multiplicative X) := IsOpenMap.id
#align is_open_map_of_add isOpenMap_ofAdd

theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X → X) := IsOpenMap.id
#align is_open_map_to_add isOpenMap_toAdd

theorem isClosedMap_ofMul : IsClosedMap (ofMul : X → Additive X) := IsClosedMap.id
#align is_closed_map_of_mul isClosedMap_ofMul

theorem isClosedMap_toMul : IsClosedMap (toMul : Additive X → X) := IsClosedMap.id
#align is_closed_map_to_mul isClosedMap_toMul

theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : X → Multiplicative X) := IsClosedMap.id
#align is_closed_map_of_add isClosedMap_ofAdd

theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X → X) := IsClosedMap.id
#align is_closed_map_to_add isClosedMap_toAdd

theorem nhds_ofMul (x : X) : 𝓝 (ofMul x) = map ofMul (𝓝 x) := rfl
#align nhds_of_mul nhds_ofMul

theorem nhds_ofAdd (x : X) : 𝓝 (ofAdd x) = map ofAdd (𝓝 x) := rfl
#align nhds_of_add nhds_ofAdd

theorem nhds_toMul (x : Additive X) : 𝓝 (toMul x) = map toMul (𝓝 x) := rfl
#align nhds_to_mul nhds_toMul

theorem nhds_toAdd (x : Multiplicative X) : 𝓝 (toAdd x) = map toAdd (𝓝 x) := rfl
#align nhds_to_add nhds_toAdd

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/


section

variable [TopologicalSpace X]

open OrderDual

instance : TopologicalSpace Xᵒᵈ := ‹TopologicalSpace X›
instance [DiscreteTopology X] : DiscreteTopology Xᵒᵈ := ‹DiscreteTopology X›

theorem continuous_toDual : Continuous (toDual : X → Xᵒᵈ) := continuous_id
#align continuous_to_dual continuous_toDual

theorem continuous_ofDual : Continuous (ofDual : Xᵒᵈ → X) := continuous_id
#align continuous_of_dual continuous_ofDual

theorem isOpenMap_toDual : IsOpenMap (toDual : X → Xᵒᵈ) := IsOpenMap.id
#align is_open_map_to_dual isOpenMap_toDual

theorem isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ → X) := IsOpenMap.id
#align is_open_map_of_dual isOpenMap_ofDual

theorem isClosedMap_toDual : IsClosedMap (toDual : X → Xᵒᵈ) := IsClosedMap.id
#align is_closed_map_to_dual isClosedMap_toDual

theorem isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ → X) := IsClosedMap.id
#align is_closed_map_of_dual isClosedMap_ofDual

theorem nhds_toDual (x : X) : 𝓝 (toDual x) = map toDual (𝓝 x) := rfl
#align nhds_to_dual nhds_toDual

theorem nhds_ofDual (x : X) : 𝓝 (ofDual x) = map ofDual (𝓝 x) := rfl
#align nhds_of_dual nhds_ofDual

end

theorem Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
    {x : X} (hs : V ∈ 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V ∈ 𝓝 x :=
  preimage_nhds_coinduced hs
#align quotient.preimage_mem_nhds Quotient.preimage_mem_nhds

/-- The image of a dense set under `Quotient.mk'` is a dense set. -/
theorem Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  Quotient.surjective_Quotient_mk''.denseRange.dense_image continuous_coinduced_rng H
#align dense.quotient Dense.quotient

/-- The composition of `Quotient.mk'` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y → X} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  Quotient.surjective_Quotient_mk''.denseRange.comp hf continuous_coinduced_rng
#align dense_range.quotient DenseRange.quotient

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
#align sum.discrete_topology Sum.discreteTopology

instance Sigma.discreteTopology {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [h : ∀ i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y) :=
  ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩
#align sigma.discrete_topology Sigma.discreteTopology

section Top

variable [TopologicalSpace X]

/-
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set X) (x : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 x ↔ ∃ u ∈ 𝓝 (x : X), Subtype.val ⁻¹' u ⊆ t :=
  mem_nhds_induced _ x t
#align mem_nhds_subtype mem_nhds_subtype

theorem nhds_subtype (s : Set X) (x : { x // x ∈ s }) : 𝓝 x = comap (↑) (𝓝 (x : X)) :=
  nhds_induced _ x
#align nhds_subtype nhds_subtype

theorem nhdsWithin_subtype_eq_bot_iff {s t : Set X} {x : s} :
    𝓝[((↑) : s → X) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap, nhdsWithin, nhdsWithin, comap_inf, comap_principal,
    nhds_induced]
#align nhds_within_subtype_eq_bot_iff nhdsWithin_subtype_eq_bot_iff

theorem nhds_ne_subtype_eq_bot_iff {S : Set X} {x : S} :
    𝓝[≠] x = ⊥ ↔ 𝓝[≠] (x : X) ⊓ 𝓟 S = ⊥ := by
  rw [← nhdsWithin_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
    Subtype.coe_injective.preimage_image]
#align nhds_ne_subtype_eq_bot_iff nhds_ne_subtype_eq_bot_iff

theorem nhds_ne_subtype_neBot_iff {S : Set X} {x : S} :
    (𝓝[≠] x).NeBot ↔ (𝓝[≠] (x : X) ⊓ 𝓟 S).NeBot := by
  rw [neBot_iff, neBot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]
#align nhds_ne_subtype_ne_bot_iff nhds_ne_subtype_neBot_iff

theorem discreteTopology_subtype_iff {S : Set X} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]
#align discrete_topology_subtype_iff discreteTopology_subtype_iff

end Top

/-- A type synonym equipped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def CofiniteTopology (X : Type*) := X

#align cofinite_topology CofiniteTopology

namespace CofiniteTopology

/-- The identity equivalence between `` and `CofiniteTopology `. -/
def of : X ≃ CofiniteTopology X :=
  Equiv.refl X
#align cofinite_topology.of CofiniteTopology.of

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
#align cofinite_topology.is_open_iff CofiniteTopology.isOpen_iff

theorem isOpen_iff' {s : Set (CofiniteTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]
#align cofinite_topology.is_open_iff' CofiniteTopology.isOpen_iff'

theorem isClosed_iff {s : Set (CofiniteTopology X)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]
#align cofinite_topology.is_closed_iff CofiniteTopology.isClosed_iff

theorem nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure x ⊔ cofinite := by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩
#align cofinite_topology.nhds_eq CofiniteTopology.nhds_eq

theorem mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]
#align cofinite_topology.mem_nhds_iff CofiniteTopology.mem_nhds_iff

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

-- Porting note (#11215): TODO: Lean 4 fails to deduce implicit args
@[simp] theorem continuous_prod_mk {f : X → Y} {g : X → Z} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  (@continuous_inf_rng X (Y × Z) _ _ (TopologicalSpace.induced Prod.fst _)
    (TopologicalSpace.induced Prod.snd _)).trans <|
    continuous_induced_rng.and continuous_induced_rng
#align continuous_prod_mk continuous_prod_mk

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst X Y) :=
  (continuous_prod_mk.1 continuous_id).1
#align continuous_fst continuous_fst

/-- Postcomposing `f` with `Prod.fst` is continuous -/
@[fun_prop]
theorem Continuous.fst {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).1 :=
  continuous_fst.comp hf
#align continuous.fst Continuous.fst

/-- Precomposing `f` with `Prod.fst` is continuous -/
theorem Continuous.fst' {f : X → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.fst :=
  hf.comp continuous_fst
#align continuous.fst' Continuous.fst'

theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
  continuous_fst.continuousAt
#align continuous_at_fst continuousAt_fst

/-- Postcomposing `f` with `Prod.fst` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.fst {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).1) x :=
  continuousAt_fst.comp hf
#align continuous_at.fst ContinuousAt.fst

/-- Precomposing `f` with `Prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : X → Z} {x : X} {y : Y} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X × Y => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst
#align continuous_at.fst' ContinuousAt.fst'

/-- Precomposing `f` with `Prod.fst` is continuous at `x : X × Y` -/
theorem ContinuousAt.fst'' {f : X → Z} {x : X × Y} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : X × Y => f x.fst) x :=
  hf.comp continuousAt_fst
#align continuous_at.fst'' ContinuousAt.fst''

theorem Filter.Tendsto.fst_nhds {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).1) l (𝓝 <| p.1) :=
  continuousAt_fst.tendsto.comp h

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd X Y) :=
  (continuous_prod_mk.1 continuous_id).2
#align continuous_snd continuous_snd

/-- Postcomposing `f` with `Prod.snd` is continuous -/
@[fun_prop]
theorem Continuous.snd {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).2 :=
  continuous_snd.comp hf
#align continuous.snd Continuous.snd

/-- Precomposing `f` with `Prod.snd` is continuous -/
theorem Continuous.snd' {f : Y → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.snd :=
  hf.comp continuous_snd
#align continuous.snd' Continuous.snd'

theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
  continuous_snd.continuousAt
#align continuous_at_snd continuousAt_snd

/-- Postcomposing `f` with `Prod.snd` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.snd {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).2) x :=
  continuousAt_snd.comp hf
#align continuous_at.snd ContinuousAt.snd

/-- Precomposing `f` with `Prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : Y → Z} {x : X} {y : Y} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : X × Y => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd
#align continuous_at.snd' ContinuousAt.snd'

/-- Precomposing `f` with `Prod.snd` is continuous at `x : X × Y` -/
theorem ContinuousAt.snd'' {f : Y → Z} {x : X × Y} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : X × Y => f x.snd) x :=
  hf.comp continuousAt_snd
#align continuous_at.snd'' ContinuousAt.snd''

theorem Filter.Tendsto.snd_nhds {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).2) l (𝓝 <| p.2) :=
  continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]
theorem Continuous.prod_mk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_prod_mk.2 ⟨hf, hg⟩
#align continuous.prod_mk Continuous.prod_mk

@[continuity]
theorem Continuous.Prod.mk (x : X) : Continuous fun y : Y => (x, y) :=
  continuous_const.prod_mk continuous_id
#align continuous.prod.mk Continuous.Prod.mk

@[continuity]
theorem Continuous.Prod.mk_left (y : Y) : Continuous fun x : X => (x, y) :=
  continuous_id.prod_mk continuous_const
#align continuous.prod.mk_left Continuous.Prod.mk_left

/-- If `f x y` is continuous in `x` for all `y ∈ s`,
then the set of `x` such that `f x` maps `s` to `t` is closed. -/
lemma IsClosed.setOf_mapsTo {α : Type*} {f : X → α → Z} {s : Set α} {t : Set Z} (ht : IsClosed t)
    (hf : ∀ a ∈ s, Continuous (f · a)) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, setOf_forall] using isClosed_biInter fun y hy ↦ ht.preimage (hf y hy)

theorem Continuous.comp₂ {g : X × Y → Z} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) : Continuous fun w => g (e w, f w) :=
  hg.comp <| he.prod_mk hf
#align continuous.comp₂ Continuous.comp₂

theorem Continuous.comp₃ {g : X × Y × Z → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) :
    Continuous fun w => g (e w, f w, k w) :=
  hg.comp₂ he <| hf.prod_mk hk
#align continuous.comp₃ Continuous.comp₃

theorem Continuous.comp₄ {g : X × Y × Z × ζ → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) {l : W → ζ}
    (hl : Continuous l) : Continuous fun w => g (e w, f w, k w, l w) :=
  hg.comp₃ he hf <| hk.prod_mk hl
#align continuous.comp₄ Continuous.comp₄

@[continuity]
theorem Continuous.prod_map {f : Z → X} {g : W → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun p : Z × W => (f p.1, g p.2) :=
  hf.fst'.prod_mk hg.snd'
#align continuous.prod_map Continuous.prod_map

/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta1; haveI := tb1; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_left₂ continuous_inf_dom_left₂

/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta2; haveI := tb2; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_right₂ continuous_inf_dom_right₂

/-- A version of `continuous_sInf_dom` for binary functions -/
theorem continuous_sInf_dom₂ {X Y Z} {f : X → Y → Z} {tas : Set (TopologicalSpace X)}
    {tbs : Set (TopologicalSpace Y)} {tX : TopologicalSpace X} {tY : TopologicalSpace Y}
    {tc : TopologicalSpace Z} (hX : tX ∈ tas) (hY : tY ∈ tbs)
    (hf : Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := sInf tas; haveI := sInf tbs;
      exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prod_map _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id
#align continuous_Inf_dom₂ continuous_sInf_dom₂

theorem Filter.Eventually.prod_inl_nhds {p : X → Prop} {x : X} (h : ∀ᶠ x in 𝓝 x, p x) (y : Y) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).1 :=
  continuousAt_fst h
#align filter.eventually.prod_inl_nhds Filter.Eventually.prod_inl_nhds

theorem Filter.Eventually.prod_inr_nhds {p : Y → Prop} {y : Y} (h : ∀ᶠ x in 𝓝 y, p x) (x : X) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).2 :=
  continuousAt_snd h
#align filter.eventually.prod_inr_nhds Filter.Eventually.prod_inr_nhds

theorem Filter.Eventually.prod_mk_nhds {px : X → Prop} {x} (hx : ∀ᶠ x in 𝓝 x, px x) {py : Y → Prop}
    {y} (hy : ∀ᶠ y in 𝓝 y, py y) : ∀ᶠ p in 𝓝 (x, y), px (p : X × Y).1 ∧ py p.2 :=
  (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)
#align filter.eventually.prod_mk_nhds Filter.Eventually.prod_mk_nhds

theorem continuous_swap : Continuous (Prod.swap : X × Y → Y × X) :=
  continuous_snd.prod_mk continuous_fst
#align continuous_swap continuous_swap

lemma isClosedMap_swap : IsClosedMap (Prod.swap : X × Y → Y × X) := fun s hs ↦ by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

theorem Continuous.uncurry_left {f : X → Y → Z} (x : X) (h : Continuous (uncurry f)) :
    Continuous (f x) :=
  h.comp (Continuous.Prod.mk _)
#align continuous_uncurry_left Continuous.uncurry_left

theorem Continuous.uncurry_right {f : X → Y → Z} (y : Y) (h : Continuous (uncurry f)) :
    Continuous fun a => f a y :=
  h.comp (Continuous.Prod.mk_left _)
#align continuous_uncurry_right Continuous.uncurry_right

-- 2024-03-09
@[deprecated] alias continuous_uncurry_left := Continuous.uncurry_left
@[deprecated] alias continuous_uncurry_right := Continuous.uncurry_right

theorem continuous_curry {g : X × Y → Z} (x : X) (h : Continuous g) : Continuous (curry g x) :=
  Continuous.uncurry_left x h
#align continuous_curry continuous_curry

theorem IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)
#align is_open.prod IsOpen.prod

-- Porting note (#11215): TODO: Lean fails to find `t₁` and `t₂` by unification
theorem nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y := by
  dsimp only [SProd.sprod]
  rw [Filter.prod, instTopologicalSpaceProd, nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _), nhds_induced, nhds_induced]
#align nhds_prod_eq nhds_prod_eq

-- Porting note: moved from `Topology.ContinuousOn`
theorem nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) :
    𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y := by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]
#align nhds_within_prod_eq nhdsWithin_prod_eq

#noalign continuous_uncurry_of_discrete_topology

theorem mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u ∈ 𝓝 x, ∃ v ∈ 𝓝 y, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]
#align mem_nhds_prod_iff mem_nhds_prod_iff

theorem mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y} :
    s ∈ 𝓝[tx ×ˢ ty] (x, y) ↔ ∃ u ∈ 𝓝[tx] x, ∃ v ∈ 𝓝[ty] y, u ×ˢ v ⊆ s := by
  rw [nhdsWithin_prod_eq, mem_prod_iff]

-- Porting note: moved up
theorem Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX → Prop} {py : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis px sx)
    (hy : (𝓝 y).HasBasis py sy) :
    (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2 := by
  rw [nhds_prod_eq]
  exact hx.prod hy
#align filter.has_basis.prod_nhds Filter.HasBasis.prod_nhds

-- Porting note: moved up
theorem Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX → Prop} {pY : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX sx)
    (hy : (𝓝 p.2).HasBasis pY sy) :
    (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧ pY i.2) fun i => sx i.1 ×ˢ sy i.2 :=
  hx.prod_nhds hy
#align filter.has_basis.prod_nhds' Filter.HasBasis.prod_nhds'

theorem mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧ u ×ˢ v ⊆ s :=
  ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans <| by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]
#align mem_nhds_prod_iff' mem_nhds_prod_iff'

theorem Prod.tendsto_iff {X} (seq : X → Y × Z) {f : Filter X} (p : Y × Z) :
    Tendsto seq f (𝓝 p) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd) := by
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']
#align prod.tendsto_iff Prod.tendsto_iff

instance [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq, nhds_discrete X, nhds_discrete Y, prod_pure_pure]

theorem prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} :
    s ×ˢ t ∈ 𝓝 (x, y) ↔ s ∈ 𝓝 x ∧ t ∈ 𝓝 y := by rw [nhds_prod_eq, prod_mem_prod_iff]
#align prod_mem_nhds_iff prod_mem_nhds_iff

theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s ∈ 𝓝 x) (hy : t ∈ 𝓝 y) :
    s ×ˢ t ∈ 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩
#align prod_mem_nhds prod_mem_nhds

theorem isOpen_setOf_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_setOf_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩
#align is_open_set_of_disjoint_nhds_nhds isOpen_setOf_disjoint_nhds_nhds

theorem Filter.Eventually.prod_nhds {p : X → Prop} {q : Y → Prop} {x : X} {y : Y}
    (hx : ∀ᶠ x in 𝓝 x, p x) (hy : ∀ᶠ y in 𝓝 y, q y) : ∀ᶠ z : X × Y in 𝓝 (x, y), p z.1 ∧ q z.2 :=
  prod_mem_nhds hx hy
#align filter.eventually.prod_nhds Filter.Eventually.prod_nhds

theorem nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq]; rfl
#align nhds_swap nhds_swap

theorem Filter.Tendsto.prod_mk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y}
    (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) :
    Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y)) := by
  rw [nhds_prod_eq]; exact Filter.Tendsto.prod_mk hx hy
#align filter.tendsto.prod_mk_nhds Filter.Tendsto.prod_mk_nhds

theorem Filter.Eventually.curry_nhds {p : X × Y → Prop} {x : X} {y : Y}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry
#align filter.eventually.curry_nhds Filter.Eventually.curry_nhds

@[fun_prop]
theorem ContinuousAt.prod {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg
#align continuous_at.prod ContinuousAt.prod

theorem ContinuousAt.prod_map {f : X → Z} {g : Y → W} {p : X × Y} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (fun p : X × Y => (f p.1, g p.2)) p :=
  hf.fst''.prod hg.snd''
#align continuous_at.prod_map ContinuousAt.prod_map

theorem ContinuousAt.prod_map' {f : X → Z} {g : Y → W} {x : X} {y : Y} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (fun p : X × Y => (f p.1, g p.2)) (x, y) :=
  hf.fst'.prod hg.snd'
#align continuous_at.prod_map' ContinuousAt.prod_map'

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
  let G := generateFrom  (image2  (·  ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun g ⟨u, hu, v, hv, g_eq⟩ =>
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
#align prod_generate_from_generate_from_eq prod_generateFrom_generateFrom_eq

-- todo: use the previous lemma?
theorem prod_eq_generateFrom :
    instTopologicalSpaceProd =
      generateFrom { g | ∃ (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun g ⟨s, t, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨t, univ, by simpa [Set.prod_eq] using ht⟩)
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨univ, t, by simpa [Set.prod_eq] using ht⟩))
#align prod_eq_generate_from prod_eq_generateFrom

-- Porting note (#11215): TODO: align with `mem_nhds_prod_iff'`
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  isOpen_iff_mem_nhds.trans <| by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]
#align is_open_prod_iff isOpen_prod_iff

/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced (f : X → Y) (g : Z → W) :
    @instTopologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instTopologicalSpaceProd := by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl
#align prod_induced_induced prod_induced_induced

#noalign continuous_uncurry_of_discrete_topology_left

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (X × X)} {x : X} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx
#align exists_nhds_square exists_nhds_square

/-- `Prod.fst` maps neighborhood of `x : X × Y` within the section `Prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl
#align map_fst_nhds_within map_fst_nhdsWithin

@[simp]
theorem map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuousAt_fst <| (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)
#align map_fst_nhds map_fst_nhds

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge
#align is_open_map_fst isOpenMap_fst

/-- `Prod.snd` maps neighborhood of `x : X × Y` within the section `Prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl
#align map_snd_nhds_within map_snd_nhdsWithin

@[simp]
theorem map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuousAt_snd <| (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)
#align map_snd_nhds map_snd_nhds

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge
#align is_open_map_snd isOpenMap_snd

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
      · show IsOpen s
        rw [← fst_image_prod s st.2]
        exact isOpenMap_fst _ H
      · show IsOpen t
        rw [← snd_image_prod st.1 t]
        exact isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false_iff] at H
      exact H.1.prod H.2
#align is_open_prod_iff' isOpen_prod_iff'

theorem closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]
#align closure_prod_eq closure_prod_eq

theorem interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]
#align interior_prod_eq interior_prod_eq

theorem frontier_prod_eq (s : Set X) (t : Set Y) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]
#align frontier_prod_eq frontier_prod_eq

@[simp]
theorem frontier_prod_univ_eq (s : Set X) :
    frontier (s ×ˢ (univ : Set Y)) = frontier s ×ˢ univ := by
  simp [frontier_prod_eq]
#align frontier_prod_univ_eq frontier_prod_univ_eq

@[simp]
theorem frontier_univ_prod_eq (s : Set Y) :
    frontier ((univ : Set X) ×ˢ s) = univ ×ˢ frontier s := by
  simp [frontier_prod_eq]
#align frontier_univ_prod_eq frontier_univ_prod_eq

theorem map_mem_closure₂ {f : X → Y → Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf : Continuous (uncurry f)) (hx : x ∈ closure s) (hy : y ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f x y ∈ closure u :=
  have H₁ : (x, y) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁
#align map_mem_closure₂ map_mem_closure₂

theorem IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_isClosed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]
#align is_closed.prod IsClosed.prod

/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩
#align dense.prod Dense.prod

/-- If `f` and `g` are maps with dense range, then `Prod.map f g` has dense range. -/
theorem DenseRange.prod_map {ι : Type*} {κ : Type*} {f : ι → Y} {g : κ → Z} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using hf.prod hg
#align dense_range.prod_map DenseRange.prod_map

theorem Inducing.prod_map {f : X → Y} {g : Z → W} (hf : Inducing f) (hg : Inducing g) :
    Inducing (Prod.map f g) :=
  inducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]
#align inducing.prod_mk Inducing.prod_map

@[simp]
theorem inducing_const_prod {x : X} {f : Y → Z} : (Inducing fun x' => (x, f x')) ↔ Inducing f := by
  simp_rw [inducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose, Function.comp,
    induced_const, top_inf_eq]
#align inducing_const_prod inducing_const_prod

@[simp]
theorem inducing_prod_const {y : Y} {f : X → Z} : (Inducing fun x => (f x, y)) ↔ Inducing f := by
  simp_rw [inducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose, Function.comp,
    induced_const, inf_top_eq]
#align inducing_prod_const inducing_prod_const

theorem Embedding.prod_map {f : X → Y} {g : Z → W} (hf : Embedding f) (hg : Embedding g) :
    Embedding (Prod.map f g) :=
  { hf.toInducing.prod_map hg.toInducing with
    inj := fun ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ => by simp [hf.inj.eq_iff, hg.inj.eq_iff] }
#align embedding.prod_mk Embedding.prod_map

protected theorem IsOpenMap.prod {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap fun p : X × Z => (f p.1, g p.2) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq]
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)
#align is_open_map.prod IsOpenMap.prod

protected theorem OpenEmbedding.prod {f : X → Y} {g : Z → W} (hf : OpenEmbedding f)
    (hg : OpenEmbedding g) : OpenEmbedding fun x : X × Z => (f x.1, g x.2) :=
  openEmbedding_of_embedding_open (hf.1.prod_map hg.1) (hf.isOpenMap.prod hg.isOpenMap)
#align open_embedding.prod OpenEmbedding.prod

theorem embedding_graph {f : X → Y} (hf : Continuous f) : Embedding fun x => (x, f x) :=
  embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id
#align embedding_graph embedding_graph

theorem embedding_prod_mk (x : X) : Embedding (Prod.mk x : Y → X × Y) :=
  embedding_of_embedding_compose (Continuous.Prod.mk x) continuous_snd embedding_id

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
#align continuous_sum_dom continuous_sum_dom

theorem continuous_sum_elim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom
#align continuous_sum_elim continuous_sum_elim

@[continuity]
theorem Continuous.sum_elim {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sum_elim.2 ⟨hf, hg⟩
#align continuous.sum_elim Continuous.sum_elim

@[continuity]
theorem continuous_isLeft : Continuous (isLeft : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity]
theorem continuous_isRight : Continuous (isRight : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity]
-- Porting note: the proof was `continuous_sup_rng_left continuous_coinduced_rng`
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩
#align continuous_inl continuous_inl

@[continuity]
-- Porting note: the proof was `continuous_sup_rng_right continuous_coinduced_rng`
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩
#align continuous_inr continuous_inr

theorem isOpen_sum_iff {s : Set (X ⊕ Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl
#align is_open_sum_iff isOpen_sum_iff

-- Porting note (#10756): new theorem
theorem isClosed_sum_iff {s : Set (X ⊕ Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]
#align is_open_map_inl isOpenMap_inl

theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]
#align is_open_map_inr isOpenMap_inr

theorem openEmbedding_inl : OpenEmbedding (@inl X Y) :=
  openEmbedding_of_continuous_injective_open continuous_inl inl_injective isOpenMap_inl
#align open_embedding_inl openEmbedding_inl

theorem openEmbedding_inr : OpenEmbedding (@inr X Y) :=
  openEmbedding_of_continuous_injective_open continuous_inr inr_injective isOpenMap_inr
#align open_embedding_inr openEmbedding_inr

theorem embedding_inl : Embedding (@inl X Y) :=
  openEmbedding_inl.1
#align embedding_inl embedding_inl

theorem embedding_inr : Embedding (@inr X Y) :=
  openEmbedding_inr.1
#align embedding_inr embedding_inr

theorem isOpen_range_inl : IsOpen (range (inl : X → X ⊕ Y)) :=
  openEmbedding_inl.2
#align is_open_range_inl isOpen_range_inl

theorem isOpen_range_inr : IsOpen (range (inr : Y → X ⊕ Y)) :=
  openEmbedding_inr.2
#align is_open_range_inr isOpen_range_inr

theorem isClosed_range_inl : IsClosed (range (inl : X → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr
#align is_closed_range_inl isClosed_range_inl

theorem isClosed_range_inr : IsClosed (range (inr : Y → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl
#align is_closed_range_inr isClosed_range_inr

theorem closedEmbedding_inl : ClosedEmbedding (inl : X → X ⊕ Y) :=
  ⟨embedding_inl, isClosed_range_inl⟩
#align closed_embedding_inl closedEmbedding_inl

theorem closedEmbedding_inr : ClosedEmbedding (inr : Y → X ⊕ Y) :=
  ⟨embedding_inr, isClosed_range_inr⟩
#align closed_embedding_inr closedEmbedding_inr

theorem nhds_inl (x : X) : 𝓝 (inl x : X ⊕ Y) = map inl (𝓝 x) :=
  (openEmbedding_inl.map_nhds_eq _).symm
#align nhds_inl nhds_inl

theorem nhds_inr (y : Y) : 𝓝 (inr y : X ⊕ Y) = map inr (𝓝 y) :=
  (openEmbedding_inr.map_nhds_eq _).symm
#align nhds_inr nhds_inr

@[simp]
theorem continuous_sum_map {f : X → Y} {g : Z → W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_elim.trans <|
    embedding_inl.continuous_iff.symm.and embedding_inr.continuous_iff.symm
#align continuous_sum_map continuous_sum_map

@[continuity]
theorem Continuous.sum_map {f : X → Y} {g : Z → W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sum_map.2 ⟨hf, hg⟩
#align continuous.sum_map Continuous.sum_map

theorem isOpenMap_sum {f : X ⊕ Y → Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp]
#align is_open_map_sum isOpenMap_sum

@[simp]
theorem isOpenMap_sum_elim {f : X → Z} {g : Y → Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]
#align is_open_map_sum_elim isOpenMap_sum_elim

theorem IsOpenMap.sum_elim {f : X → Z} {g : Y → Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sum_elim.2 ⟨hf, hg⟩
#align is_open_map.sum_elim IsOpenMap.sum_elim

end Sum

section Subtype

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {p : X → Prop}

theorem inducing_subtype_val {t : Set Y} : Inducing ((↑) : t → Y) := ⟨rfl⟩
#align inducing_coe inducing_subtype_val

theorem Inducing.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (h : Inducing (t.codRestrict f ht)) : Inducing f :=
  inducing_subtype_val.comp h
#align inducing.of_cod_restrict Inducing.of_codRestrict

theorem embedding_subtype_val : Embedding ((↑) : Subtype p → X) :=
  ⟨inducing_subtype_val, Subtype.coe_injective⟩
#align embedding_subtype_coe embedding_subtype_val

theorem closedEmbedding_subtype_val (h : IsClosed { a | p a }) :
    ClosedEmbedding ((↑) : Subtype p → X) :=
  ⟨embedding_subtype_val, by rwa [Subtype.range_coe_subtype]⟩
#align closed_embedding_subtype_coe closedEmbedding_subtype_val

@[continuity]
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom
#align continuous_subtype_val continuous_subtype_val
#align continuous_subtype_coe continuous_subtype_val

theorem Continuous.subtype_val {f : Y → Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : X) :=
  continuous_subtype_val.comp hf
#align continuous.subtype_coe Continuous.subtype_val

theorem IsOpen.openEmbedding_subtype_val {s : Set X} (hs : IsOpen s) :
    OpenEmbedding ((↑) : s → X) :=
  ⟨embedding_subtype_val, (@Subtype.range_coe _ s).symm ▸ hs⟩
#align is_open.open_embedding_subtype_coe IsOpen.openEmbedding_subtype_val

theorem IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) : s → X) :=
  hs.openEmbedding_subtype_val.isOpenMap
#align is_open.is_open_map_subtype_coe IsOpen.isOpenMap_subtype_val

theorem IsOpenMap.restrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
    IsOpenMap (s.restrict f) :=
  hf.comp hs.isOpenMap_subtype_val
#align is_open_map.restrict IsOpenMap.restrict

nonrec theorem IsClosed.closedEmbedding_subtype_val {s : Set X} (hs : IsClosed s) :
    ClosedEmbedding ((↑) : s → X) :=
  closedEmbedding_subtype_val hs
#align is_closed.closed_embedding_subtype_coe IsClosed.closedEmbedding_subtype_val

@[continuity]
theorem Continuous.subtype_mk {f : Y → X} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h
#align continuous.subtype_mk Continuous.subtype_mk

theorem Continuous.subtype_map {f : X → Y} (h : Continuous f) {q : Y → Prop}
    (hpq : ∀ x, p x → q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_val).subtype_mk _
#align continuous.subtype_map Continuous.subtype_map

theorem continuous_inclusion {s t : Set X} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_id.subtype_map h
#align continuous_inclusion continuous_inclusion

theorem continuousAt_subtype_val {p : X → Prop} {x : Subtype p} :
    ContinuousAt ((↑) : Subtype p → X) x :=
  continuous_subtype_val.continuousAt
#align continuous_at_subtype_coe continuousAt_subtype_val

theorem Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔ s ⊆ closure ((↑) '' t) := by
  rw [inducing_subtype_val.dense_iff, SetCoe.forall]
  rfl
#align subtype.dense_iff Subtype.dense_iff

-- Porting note (#10756): new lemma
theorem map_nhds_subtype_val {s : Set X} (x : s) : map ((↑) : s → X) (𝓝 x) = 𝓝[s] ↑x := by
  rw [inducing_subtype_val.map_nhds_eq, Subtype.range_val]

theorem map_nhds_subtype_coe_eq_nhds {x : X} (hx : p x) (h : ∀ᶠ x in 𝓝 x, p x) :
    map ((↑) : Subtype p → X) (𝓝 ⟨x, hx⟩) = 𝓝 x :=
  map_nhds_induced_of_mem <| by rw [Subtype.range_val]; exact h
#align map_nhds_subtype_coe_eq map_nhds_subtype_coe_eq_nhds

theorem nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x) :=
  nhds_induced _ _
#align nhds_subtype_eq_comap nhds_subtype_eq_comap

theorem tendsto_subtype_rng {Y : Type*} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p} :
    ∀ {x : Subtype p}, Tendsto f l (𝓝 x) ↔ Tendsto (fun x => (f x : X)) l (𝓝 (x : X))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; rfl
#align tendsto_subtype_rng tendsto_subtype_rng

theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ closure s ↔ (x : X) ∈ closure (((↑) : _ → X) '' s) :=
  closure_induced
#align closure_subtype closure_subtype

@[simp]
theorem continuousAt_codRestrict_iff {f : X → Y} {t : Set Y} (h1 : ∀ x, f x ∈ t) {x : X} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x :=
  inducing_subtype_val.continuousAt_iff
#align continuous_at_cod_restrict_iff continuousAt_codRestrict_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff
#align continuous_at.cod_restrict ContinuousAt.codRestrict

theorem ContinuousAt.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuousAt_subtype_val).codRestrict _
#align continuous_at.restrict ContinuousAt.restrict

theorem ContinuousAt.restrictPreimage {f : X → Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x) :
    ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _
#align continuous_at.restrict_preimage ContinuousAt.restrictPreimage

@[continuity]
theorem Continuous.codRestrict {f : X → Y} {s : Set Y} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs
#align continuous.cod_restrict Continuous.codRestrict

@[continuity]
theorem Continuous.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
    (h2 : Continuous f) : Continuous (h1.restrict f s t) :=
  (h2.comp continuous_subtype_val).codRestrict _

@[continuity]
theorem Continuous.restrictPreimage {f : X → Y} {s : Set Y} (h : Continuous f) :
    Continuous (s.restrictPreimage f) :=
  h.restrict _

theorem Inducing.codRestrict {e : X → Y} (he : Inducing e) {s : Set Y} (hs : ∀ x, e x ∈ s) :
    Inducing (codRestrict e s hs) :=
  inducing_of_inducing_compose (he.continuous.codRestrict hs) continuous_subtype_val he
#align inducing.cod_restrict Inducing.codRestrict

theorem Embedding.codRestrict {e : X → Y} (he : Embedding e) (s : Set Y) (hs : ∀ x, e x ∈ s) :
    Embedding (codRestrict e s hs) :=
  embedding_of_embedding_compose (he.continuous.codRestrict hs) continuous_subtype_val he
#align embedding.cod_restrict Embedding.codRestrict

theorem embedding_inclusion {s t : Set X} (h : s ⊆ t) : Embedding (inclusion h) :=
  embedding_subtype_val.codRestrict _ _
#align embedding_inclusion embedding_inclusion

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
theorem DiscreteTopology.of_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (_ : DiscreteTopology s) (ts : t ⊆ s) : DiscreteTopology t :=
  (embedding_inclusion ts).discreteTopology
#align discrete_topology.of_subset DiscreteTopology.of_subset

/-- Let `s` be a discrete subset of a topological space. Then the preimage of `s` by
a continuous injective map is also discrete. -/
theorem DiscreteTopology.preimage_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Set Y) [DiscreteTopology s] {f : X → Y} (hc : Continuous f)
    (hinj : Function.Injective f) : DiscreteTopology (f ⁻¹' s) :=
  DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x ↦ x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)

end Subtype

section Quotient

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {r : X → X → Prop} {s : Setoid X}

theorem quotientMap_quot_mk : QuotientMap (@Quot.mk X r) :=
  ⟨Quot.exists_rep, rfl⟩
#align quotient_map_quot_mk quotientMap_quot_mk

@[continuity]
theorem continuous_quot_mk : Continuous (@Quot.mk X r) :=
  continuous_coinduced_rng
#align continuous_quot_mk continuous_quot_mk

@[continuity]
theorem continuous_quot_lift {f : X → Y} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → Y) :=
  continuous_coinduced_dom.2 h
#align continuous_quot_lift continuous_quot_lift

theorem quotientMap_quotient_mk' : QuotientMap (@Quotient.mk' X s) :=
  quotientMap_quot_mk
#align quotient_map_quotient_mk quotientMap_quotient_mk'

theorem continuous_quotient_mk' : Continuous (@Quotient.mk' X s) :=
  continuous_coinduced_rng
#align continuous_quotient_mk continuous_quotient_mk'

theorem Continuous.quotient_lift {f : X → Y} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → Y) :=
  continuous_coinduced_dom.2 h
#align continuous.quotient_lift Continuous.quotient_lift

theorem Continuous.quotient_liftOn' {f : X → Y} (h : Continuous f)
    (hs : ∀ a b, @Setoid.r _ s a b → f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s → Y) :=
  h.quotient_lift hs
#align continuous.quotient_lift_on' Continuous.quotient_liftOn'

@[continuity] theorem Continuous.quotient_map' {t : Setoid Y} {f : X → Y} (hf : Continuous f)
    (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _
#align continuous.quotient_map' Continuous.quotient_map'

end Quotient

section Pi

variable {ι : Type*} {π : ι → Type*} {κ : Type*} [TopologicalSpace X]
  [T : ∀ i, TopologicalSpace (π i)] {f : X → ∀ i : ι, π i}

theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a => f a i := by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp]
#align continuous_pi_iff continuous_pi_iff

@[continuity, fun_prop]
theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h
#align continuous_pi continuous_pi

@[continuity, fun_prop]
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_iInf_dom continuous_induced_dom
#align continuous_apply continuous_apply

@[continuity]
theorem continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)
#align continuous_apply_apply continuous_apply_apply

theorem continuousAt_apply (i : ι) (x : ∀ i, π i) : ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).continuousAt
#align continuous_at_apply continuousAt_apply

theorem Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y → ∀ i, π i} {x : ∀ i, π i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).tendsto.comp h
#align filter.tendsto.apply Filter.Tendsto.apply_nhds

theorem nhds_pi {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_iInf, nhds_induced, Filter.pi]
#align nhds_pi nhds_pi

theorem tendsto_pi_nhds {f : Y → ∀ i, π i} {g : ∀ i, π i} {u : Filter Y} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]
#align tendsto_pi_nhds tendsto_pi_nhds

theorem continuousAt_pi {f : X → ∀ i, π i} {x : X} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds
#align continuous_at_pi continuousAt_pi

@[fun_prop]
theorem continuousAt_pi' {f : X → ∀ i, π i} {x : X} (hf : ∀ i, ContinuousAt (fun y => f y i) x) :
    ContinuousAt f x :=
  continuousAt_pi.2 hf

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
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp]

lemma Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' → ι) :
    induced (· ∘ φ) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y› :=
  induced_precomp' φ

lemma Pi.continuous_restrict (S : Set ι) :
    Continuous (S.restrict : (∀ i : ι, π i) → (∀ i : S, π i)) :=
  Pi.continuous_precomp' ((↑) : S → ι)

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
#align filter.tendsto.update Filter.Tendsto.update

theorem ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X → π i}
    (hg : ContinuousAt g x) : ContinuousAt (fun a => update (f a) i (g a)) x :=
  hf.tendsto.update i hg
#align continuous_at.update ContinuousAt.update

theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X → π i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt
#align continuous.update Continuous.update

/-- `Function.update f i x` is continuous in `(f, x)`. -/
@[continuity]
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, π j) × π i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd
#align continuous_update continuous_update

/-- `Pi.mulSingle i x` is continuous in `x`. -/
-- Porting note (#11215): TODO: restore @[continuity]
@[to_additive "`Pi.single i x` is continuous in `x`."]
theorem continuous_mulSingle [∀ i, One (π i)] [DecidableEq ι] (i : ι) :
    Continuous fun x => (Pi.mulSingle i x : ∀ i, π i) :=
  continuous_const.update _ continuous_id
#align continuous_mul_single continuous_mulSingle
#align continuous_single continuous_single

theorem Filter.Tendsto.fin_insertNth {n} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : Y → π i} {l : Filter Y} {x : π i} (hf : Tendsto f l (𝓝 x))
    {g : Y → ∀ j : Fin n, π (i.succAbove j)} {y : ∀ j, π (i.succAbove j)} (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j
#align filter.tendsto.fin_insert_nth Filter.Tendsto.fin_insertNth

theorem ContinuousAt.fin_insertNth {n} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : X → π i} {x : X} (hf : ContinuousAt f x)
    {g : X → ∀ j : Fin n, π (i.succAbove j)} (hg : ContinuousAt g x) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) x :=
  hf.tendsto.fin_insertNth i hg
#align continuous_at.fin_insert_nth ContinuousAt.fin_insertNth

theorem Continuous.fin_insertNth {n} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : X → π i} (hf : Continuous f) {g : X → ∀ j : Fin n, π (i.succAbove j)}
    (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.fin_insertNth i hg.continuousAt
#align continuous.fin_insert_nth Continuous.fin_insertNth

theorem isOpen_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)
#align is_open_set_pi isOpen_set_pi

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
#align is_open_pi_iff isOpen_pi_iff

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
#align is_open_pi_iff' isOpen_pi_iff'

theorem isClosed_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)
#align is_closed_set_pi isClosed_set_pi

theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (π i)} (a : ∀ i, π i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi
#align mem_nhds_of_pi_mem_nhds mem_nhds_of_pi_mem_nhds

theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)
#align set_pi_mem_nhds set_pi_mem_nhds

theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} (a : ∀ i, π i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]
#align set_pi_mem_nhds_iff set_pi_mem_nhds_iff

theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} :
    interior (pi I s) = I.pi fun i => interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]
#align interior_pi_set interior_pi_set

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, π a)} {x : ∀ a, π a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)
#align exists_finset_piecewise_mem_of_mem_nhds exists_finset_piecewise_mem_of_mem_nhds

theorem pi_generateFrom_eq {π : ι → Type*} {g : ∀ a, Set (Set (π a))} :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (π a)) (i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    letI := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · refine le_iInf fun i => coinduced_le_iff_le_induced.1 <| le_generateFrom fun s hs => ?_
    refine GenerateOpen.basic _ ⟨update (fun i => univ) i s, {i}, ?_⟩
    simp [hs]
#align pi_generate_from_eq pi_generateFrom_eq

theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (π a)) (i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι π fun a => generateFrom { s | IsOpen s } := by
    simp only [generateFrom_setOf_isOpen]
  _ = _ := pi_generateFrom_eq
#align pi_eq_generate_from pi_eq_generateFrom

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
    rw [← univ_pi_piecewise]
    refine GenerateOpen.basic _ ⟨_, fun a => ?_, rfl⟩
    by_cases a ∈ i <;> simp [*]
#align pi_generate_from_eq_finite pi_generateFrom_eq_finite

theorem induced_to_pi {X : Type*} (f : X → ∀ i, π i) :
    induced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance := by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp]

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_iInf_to_pi {X : Type*} (f : ∀ i, X → π i) :
    @Inducing X (∀ i, π i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x :=
  letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩
#align inducing_infi_to_pi inducing_iInf_to_pi

variable [Finite ι] [∀ i, DiscreteTopology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discreteTopology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})
#align Pi.discrete_topology Pi.discreteTopology

end Pi

section Sigma

variable {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*} [∀ i, TopologicalSpace (σ i)]
  [∀ k, TopologicalSpace (τ k)] [TopologicalSpace X]

@[continuity]
theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_iSup_rng continuous_coinduced_rng
#align continuous_sigma_mk continuous_sigmaMk

-- Porting note: the proof was `by simp only [isOpen_iSup_iff, isOpen_coinduced]`
theorem isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  delta instTopologicalSpaceSigma
  rw [isOpen_iSup_iff]
  rfl
#align is_open_sigma_iff isOpen_sigma_iff

theorem isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]
#align is_closed_sigma_iff isClosed_sigma_iff

theorem isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty
#align is_open_map_sigma_mk isOpenMap_sigmaMk

theorem isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sigma.mk ι σ i)) :=
  isOpenMap_sigmaMk.isOpen_range
#align is_open_range_sigma_mk isOpen_range_sigmaMk

theorem isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty
#align is_closed_map_sigma_mk isClosedMap_sigmaMk

theorem isClosed_range_sigmaMk {i : ι} : IsClosed (range (@Sigma.mk ι σ i)) :=
  isClosedMap_sigmaMk.isClosed_range
#align is_closed_range_sigma_mk isClosed_range_sigmaMk

theorem openEmbedding_sigmaMk {i : ι} : OpenEmbedding (@Sigma.mk ι σ i) :=
  openEmbedding_of_continuous_injective_open continuous_sigmaMk sigma_mk_injective
    isOpenMap_sigmaMk
#align open_embedding_sigma_mk openEmbedding_sigmaMk

theorem closedEmbedding_sigmaMk {i : ι} : ClosedEmbedding (@Sigma.mk ι σ i) :=
  closedEmbedding_of_continuous_injective_closed continuous_sigmaMk sigma_mk_injective
    isClosedMap_sigmaMk
#align closed_embedding_sigma_mk closedEmbedding_sigmaMk

theorem embedding_sigmaMk {i : ι} : Embedding (@Sigma.mk ι σ i) :=
  closedEmbedding_sigmaMk.1
#align embedding_sigma_mk embedding_sigmaMk

theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x) :=
  (openEmbedding_sigmaMk.map_nhds_eq x).symm
#align sigma.nhds_mk Sigma.nhds_mk

theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2) := by
  cases x
  apply Sigma.nhds_mk
#align sigma.nhds_eq Sigma.nhds_eq

theorem comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (embedding_sigmaMk.nhds_eq_comap _).symm
#align comap_sigma_mk_nhds comap_sigmaMk_nhds

theorem isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a)) := by
  rw [← biUnion_of_singleton s, preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk
#align is_open_sigma_fst_preimage isOpen_sigma_fst_preimage

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
theorem continuous_sigma_iff {f : Sigma σ → X} :
    Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ := by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom
#align continuous_sigma_iff continuous_sigma_iff

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
theorem continuous_sigma {f : Sigma σ → X} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf
#align continuous_sigma continuous_sigma

/-- A map defined on a sigma type (a.k.a. the disjoint union of an indexed family of topological
spaces) is inducing iff its restriction to each component is inducing and each the image of each
component under `f` can be separated from the images of all other components by an open set. -/
theorem inducing_sigma {f : Sigma σ → X} :
    Inducing f ↔ (∀ i, Inducing (f ∘ Sigma.mk i)) ∧
      (∀ i, ∃ U, IsOpen U ∧ ∀ x, f x ∈ U ↔ x.1 = i) := by
  refine ⟨fun h ↦ ⟨fun i ↦ h.comp embedding_sigmaMk.1, fun i ↦ ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ ↦ inducing_iff_nhds.2 fun ⟨i, x⟩ ↦ ?_
    rw [Sigma.nhds_mk, (h₁ i).nhds_eq_comap, comp_apply, ← comap_comap, map_comap_of_mem]
    rcases h₂ i with ⟨U, hUo, hU⟩
    filter_upwards [preimage_mem_comap <| hUo.mem_nhds <| (hU _).2 rfl] with y hy
    simpa [hU] using hy

@[simp 1100]
theorem continuous_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ ∀ i, Continuous (f₂ i) :=
  continuous_sigma_iff.trans <| by simp only [Sigma.map, embedding_sigmaMk.continuous_iff, comp]
#align continuous_sigma_map continuous_sigma_map

@[continuity]
theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf
#align continuous.sigma_map Continuous.sigma_map

theorem isOpenMap_sigma {f : Sigma σ → X} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp]
#align is_open_map_sigma isOpenMap_sigma

theorem isOpenMap_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  isOpenMap_sigma.trans <|
    forall_congr' fun i => (@openEmbedding_sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm
#align is_open_map_sigma_map isOpenMap_sigma_map

theorem inducing_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h₁ : Injective f₁) :
    Inducing (Sigma.map f₁ f₂) ↔ ∀ i, Inducing (f₂ i) := by
  simp only [inducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk, ← map_sigma_mk_comap h₁,
    map_inj sigma_mk_injective]
#align inducing_sigma_map inducing_sigma_map

theorem embedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    Embedding (Sigma.map f₁ f₂) ↔ ∀ i, Embedding (f₂ i) := by
  simp only [embedding_iff, Injective.sigma_map, inducing_sigma_map h, forall_and, h.sigma_map_iff]
#align embedding_sigma_map embedding_sigma_map

theorem openEmbedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    OpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, OpenEmbedding (f₂ i) := by
  simp only [openEmbedding_iff_embedding_open, isOpenMap_sigma_map, embedding_sigma_map h,
    forall_and]
#align open_embedding_sigma_map openEmbedding_sigma_map

end Sigma

section ULift

theorem ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsOpen s ↔ IsOpen (ULift.up ⁻¹' s) := by
  rw [ULift.topologicalSpace, ← Equiv.ulift_apply, ← Equiv.ulift.coinduced_symm, ← isOpen_coinduced]

theorem ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsClosed s ↔ IsClosed (ULift.up ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_iff, preimage_compl]

@[continuity]
theorem continuous_uLift_down [TopologicalSpace X] : Continuous (ULift.down : ULift.{v, u} X → X) :=
  continuous_induced_dom
#align continuous_ulift_down continuous_uLift_down

@[continuity]
theorem continuous_uLift_up [TopologicalSpace X] : Continuous (ULift.up : X → ULift.{v, u} X) :=
  continuous_induced_rng.2 continuous_id
#align continuous_ulift_up continuous_uLift_up

theorem embedding_uLift_down [TopologicalSpace X] : Embedding (ULift.down : ULift.{v, u} X → X) :=
  ⟨⟨rfl⟩, ULift.down_injective⟩
#align embedding_ulift_down embedding_uLift_down

theorem ULift.closedEmbedding_down [TopologicalSpace X] :
    ClosedEmbedding (ULift.down : ULift.{v, u} X → X) :=
  ⟨embedding_uLift_down, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩
#align ulift.closed_embedding_down ULift.closedEmbedding_down

instance [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (ULift X) :=
  embedding_uLift_down.discreteTopology

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
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s : Set X} {t : Set Y} {x : X}

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
