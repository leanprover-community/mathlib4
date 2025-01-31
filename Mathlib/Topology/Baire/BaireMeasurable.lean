/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Topology.GDelta.UniformSpace
import Mathlib.Topology.LocallyClosed
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Baire category and Baire measurable sets

This file defines some of the basic notions of Baire category and Baire measurable sets.

## Main definitions

First, we define the notation `=ᵇ`. This denotes eventual equality with respect to the filter of
`residual` sets in a topological space.

A set `s` in a topological space `α` is called a `BaireMeasurableSet` or said to have the
*property of Baire* if it satisfies either of the following equivalent conditions:

* There is a *Borel* set `u` such that `s =ᵇ u`. (This is our definition)
* There is an *open* set `u` such that `s =ᵇ u`. (See `BaireMeasurableSet.residual_eq_open`)

-/

variable (α : Type*) {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

open Topology TopologicalSpace Set

/-- Notation for `=ᶠ[residual _]`. That is, eventual equality with respect to
the filter of residual sets.-/
scoped[Topology] notation:50 f " =ᵇ " g:50 => Filter.EventuallyEq (residual _) f g

/-- Notation to say that a property of points in a topological space holds
almost everywhere in the sense of Baire category. That is, on a residual set. -/
scoped[Topology] notation3 "∀ᵇ "(...)", "r:(scoped p => Filter.Eventually p <| residual _) => r

/-- Notation to say that a property of points in a topological space holds on a non meager set. -/
scoped[Topology] notation3 "∃ᵇ "(...)", "r:(scoped p => Filter.Frequently p <| residual _) => r

variable {α}

theorem coborder_mem_residual {s : Set α} (hs : IsLocallyClosed s) : coborder s ∈ residual α :=
  residual_of_dense_open hs.isOpen_coborder dense_coborder

theorem closure_residualEq {s : Set α} (hs : IsLocallyClosed s) : closure s =ᵇ s := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [coborder_mem_residual hs] with x hx
  nth_rewrite 2 [← closure_inter_coborder (s := s)]
  simp [hx]

/-- We say a set is a `BaireMeasurableSet` if it differs from some Borel set by
a meager set. This forms a σ-algebra.

It is equivalent, and a more standard definition, to say that the set differs from
some *open* set by a meager set. See `BaireMeasurableSet.iff_residualEq_isOpen` -/
def BaireMeasurableSet (s : Set α) : Prop :=
  @MeasurableSet _ (EventuallyMeasurableSpace (borel _) (residual _)) s

variable {s t : Set α}

namespace BaireMeasurableSet

theorem of_mem_residual (h : s ∈ residual _) : BaireMeasurableSet s :=
  eventuallyMeasurableSet_of_mem_filter (α := α) h

theorem _root_.MeasurableSet.baireMeasurableSet [MeasurableSpace α] [BorelSpace α]
    (h : MeasurableSet s) : BaireMeasurableSet s := by
  borelize α
  exact h.eventuallyMeasurableSet

theorem _root_.IsOpen.baireMeasurableSet (h : IsOpen s) : BaireMeasurableSet s := by
  borelize α
  exact h.measurableSet.baireMeasurableSet

theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h

theorem of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s := MeasurableSet.of_compl h

theorem _root_.IsMeagre.baireMeasurableSet (h : IsMeagre s) : BaireMeasurableSet s :=
  (of_mem_residual h).of_compl

theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i, s i) :=
  MeasurableSet.iUnion h

theorem biUnion {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i ∈ t, s i) :=
  MeasurableSet.biUnion ht h

theorem sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs h

theorem iInter {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i, s i) :=
  MeasurableSet.iInter h

theorem biInter {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i ∈ t, s i) :=
  MeasurableSet.biInter ht h

theorem sInter {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs h

theorem union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∪ t) :=
  MeasurableSet.union hs ht

theorem inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∩ t) :=
  MeasurableSet.inter hs ht

theorem diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s \ t) :=
  MeasurableSet.diff hs ht

theorem congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t :=
  EventuallyMeasurableSet.congr (α := α) hs h.symm

end BaireMeasurableSet

open Filter

/--Any Borel set differs from some open set by a meager set. -/
theorem MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    ∃ u : Set α, IsOpen u ∧ s =ᵇ u := by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
    exact .compl <| hsU.trans <| .symm <| closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
    choose u uo su using ihf
    exact ⟨⋃ i, u i, isOpen_iUnion uo, EventuallyEq.countable_iUnion su⟩

/--Any `BaireMeasurableSet` differs from some open set by a meager set. -/
theorem BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

/--A set is Baire measurable if and only if it differs from some open set by a meager set. -/
theorem BaireMeasurableSet.iff_residualEq_isOpen :
    BaireMeasurableSet s ↔ ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u :=
  ⟨fun h => h.residualEq_isOpen , fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩

section Map

open Set

variable {f : α → β}

theorem tendsto_residual_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) :
    Tendsto f (residual α) (residual β) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)

/-- The preimage of a meager set under a continuous open map is meager. -/
theorem IsMeagre.preimage_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s) :=
  tendsto_residual_of_isOpenMap hc ho h

/-- The preimage of a `BaireMeasurableSet` under a continuous open map is Baire measurable. -/
theorem BaireMeasurableSet.preimage (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : BaireMeasurableSet s) : BaireMeasurableSet (f⁻¹' s) := by
  rcases h with ⟨u, hu, hsu⟩
  refine ⟨f ⁻¹' u, ?_, hsu.filter_mono <| tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu

theorem Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β := by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap

end Map

section KU

/-!
### The Kuratowski Ulam Theorem

The Kuratowski Ulam Theorem is an analogue of Fubini's theorem for the filter of `residual` sets
in second countable topological spaces.

We prove several versions in this section.
-/

variable {s : Set (α × β)}

/-- One direction of the *Kuratowski-Ulam Theorem*. If a set `s` is residual in a product space,
residually-many sections are residual.

Expressed here using the `curry` operation on Filters. -/
theorem curry_le_residual [SecondCountableTopology β] :
    (residual α).curry (residual β) ≤ residual (α × β) := by
  intro a ha
  rcases mem_residual_iff.mp ha with ⟨S, So, Sd, Sct, Sa⟩
  refine mem_of_superset ?_ Sa
  rw [countable_sInter_mem Sct]
  intro s hs
  rw [mem_curry_iff]
  apply Eventually.mono _ (fun x h => residual_of_dense_open ((So _ hs).curry_left _) h)
  simp_rw [(isBasis_countableBasis _).dense_iff]
  rw [eventually_countable_ball (countable_countableBasis β)]
  --for some reason this doesn't work with simp_rw. It worked in an earlier version!
  simp_rw [eventually_all]
  intro t ht tnon
  have : {x | (t ∩ (x, ·) ⁻¹' s).Nonempty} = (Prod.fst) '' ((univ ×ˢ t) ∩ s) := by
    ext x
    simp only [mem_setOf_eq, mem_image, mem_inter_iff, mem_prod, mem_univ, true_and, Prod.exists,
      exists_and_right, exists_eq_right]
    rfl
  rw [eventually_iff, this]
  apply residual_of_dense_open (isOpenMap_fst _
    ((isOpen_univ.prod (isOpen_of_mem_countableBasis ht)).inter (So _ hs)))
  simp_rw [dense_iff_inter_open] at *
  intro u hu unon
  rcases Sd _ hs (u ×ˢ t) (hu.prod (isOpen_of_mem_countableBasis ht)) (unon.prod tnon)
    with ⟨⟨x, y⟩, hxy⟩
  exact ⟨x, hxy.1.1, (x, y), ⟨⟨⟨trivial, hxy.1.2⟩, hxy.2⟩, rfl⟩⟩

/-- One direction of the *Kuratowski-Ulam Theorem*. If a set `s` is residual in a product space,
residually-many sections are residual. -/
theorem eventually_eventually_left_of_mem_residual [SecondCountableTopology β]
    (hs : s ∈ residual (α × β)) : ∀ᵇ x : α, ∀ᵇ y : β, (x, y) ∈ s := curry_le_residual hs

/-- One direction of the *Kuratowski-Ulam Theorem*. If a set `s` is residual in a product space,
residually-many sections are residual. -/
theorem eventually_eventually_right_of_mem_residual [SecondCountableTopology α]
    (hs : s ∈ residual (α × β)) : ∀ᵇ y : β, ∀ᵇ x : α, (x, y) ∈ s :=
  eventually_eventually_left_of_mem_residual
    (tendsto_residual_of_isOpenMap continuous_swap isOpenMap_swap hs)

variable {s : Set α} {t : Set β}

theorem mem_residual_prod (hs : s ∈ residual _) (ht : t ∈ residual _) : s ×ˢ t ∈ residual _ :=
  inter_mem (tendsto_residual_of_isOpenMap continuous_fst isOpenMap_fst hs)
            (tendsto_residual_of_isOpenMap continuous_snd isOpenMap_snd ht)

theorem IsMeagre.prod_left (hs : IsMeagre s) (t : Set β) : IsMeagre (s ×ˢ t) := by
  apply mem_of_superset <| mem_residual_prod hs univ_mem
  rintro x ⟨_, -⟩ ⟨_, -⟩
  contradiction

theorem IsMeagre.prod_right (ht : IsMeagre t) (s : Set α) : IsMeagre (s ×ˢ t) := by
  convert (ht.prod_left s).preimage_of_isOpenMap continuous_swap isOpenMap_swap
  exact (preimage_swap_prod _ _).symm

variable {s : Set (α × β)}

namespace BaireMeasurableSet

/-- If a set `s` is Baire measurable in a product space, residually-many sections are
Baire measurable. -/
theorem baireMeasurableSet_curry_left [SecondCountableTopology β]
    (hs : BaireMeasurableSet s) : ∀ᵇ x : α, BaireMeasurableSet ((x, ·) ⁻¹' s) := by
  simp_rw [BaireMeasurableSet.iff_residualEq_isOpen] at *
  rcases hs with ⟨u, hu, su⟩
  apply Eventually.mono (eventually_eventually_left_of_mem_residual su)
  exact fun x hx => ⟨_, hu.curry_left x, hx⟩

/-- If a set `s` is Baire measurable in a product space, residually-many sections are
Baire measurable. -/
theorem baireMeasurableSet_curry_right [SecondCountableTopology α]
    (hs : BaireMeasurableSet s) : ∀ᵇ y : β, BaireMeasurableSet ((·, y) ⁻¹' s) :=
  (hs.preimage continuous_swap isOpenMap_swap).baireMeasurableSet_curry_left

variable [SecondCountableTopology α] [SecondCountableTopology β]

/-- One direction of the *Kuratowski-Ulam Theorem*. If a set `s` is non-meagre and Baire
measurable in a product space, non-meagerly many sections are non-meagre. -/
theorem frequently_curry_of_not_isMeagre (hm : BaireMeasurableSet s)
    (hn : ¬ IsMeagre s) : ∃ᶠ x in (residual α).curry (residual β), x ∈ s := by
  wlog ho : IsOpen s
  · rcases hm.residualEq_isOpen with ⟨u, hu, su⟩
    exact (this hu.baireMeasurableSet (Frequently.of_eventuallyEq hn su.symm) hu).of_eventuallyEq
      (eventually_eventually_left_of_mem_residual su)
  rcases ((isBasis_countableBasis α).prod (isBasis_countableBasis β)).open_eq_sUnion ho with
    ⟨S, hS, rfl⟩
  rcases exists_of_not_isMeagre_sUnion (Countable.mono hS <|
    (countable_countableBasis _).image2 (countable_countableBasis _) _) hn with ⟨u, uS, hu⟩
  rcases hS uS with ⟨s, -, t, -, rfl⟩
  refine Frequently.mono ?_ (subset_sUnion_of_mem uS)
  rw [frequently_curry_prod_iff]
  exact ⟨fun h => hu <| IsMeagre.prod_left h _ ,
    fun h => hu <| IsMeagre.prod_right h _ ⟩

/--The *Kuratowski-Ulam Theorem*. If a set `s` Baire measurable in a product space,
it is residual if and only if residually many sections are residual.

Expressed here using the `curry` operation on filters. -/
theorem mem_curry_iff_mem_residual (hs : BaireMeasurableSet s) :
    s ∈ (residual _).curry (residual _) ↔ s ∈ residual _ := by
  constructor
  · contrapose
    rw [← compl_compl s]
    exact hs.compl.frequently_curry_of_not_isMeagre
  apply curry_le_residual

/--The *Kuratowski-Ulam Theorem*. If a set `s` Baire measurable in a product space,
it is residual if and only if residually many sections are residual. -/
theorem eventually_eventually_left_iff_mem_residual
    (hs : BaireMeasurableSet s) :
    (∀ᵇ x : α, ∀ᵇ y : β, (x, y) ∈ s) ↔ s ∈ residual _ := hs.mem_curry_iff_mem_residual

/--The *Kuratowski-Ulam Theorem*. If a set `s` Baire measurable in a product space,
it is residual if and only if residually many sections are residual. -/
theorem eventually_eventually_right_iff_mem_residual
    (hs : BaireMeasurableSet s) :
    (∀ᵇ y : β, ∀ᵇ x : α, (x, y) ∈ s) ↔ s ∈ residual _ := by
  rw [← (Homeomorph.prodComm β α).residual_map_eq]
  exact (hs.preimage continuous_swap isOpenMap_swap).eventually_eventually_left_iff_mem_residual

/-- Part of the *Kuratowski-Ulam Theorem*. If a set `s` is Baire measurable in a product space,
one can "Change the order of integration" when asking whether residually many sections are
residual. -/
theorem eventually_eventually_swap (hs : BaireMeasurableSet s) :
    (∀ᵇ x : α, ∀ᵇ y : β, (x, y) ∈ s) ↔ (∀ᵇ y : β, ∀ᵇ x : α, (x, y) ∈ s) :=
  hs.eventually_eventually_left_iff_mem_residual.trans
    hs.eventually_eventually_right_iff_mem_residual.symm

end BaireMeasurableSet

end KU
