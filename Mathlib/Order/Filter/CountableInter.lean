/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module order.filter.countable_Inter
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Countable

/-!
# Filters with countable intersection property

In this file we define `CountableInterFilter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `Mathlib.Topology.MetricSpace.Baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.

We reformulate the definition in terms of indexed intersection and in terms of `filter.eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `Filter.principal`, `Filter.map`,
`Filter.comap`, `Inf.inf`). We also provide a custom constructor `Filter.ofCountableInter`
that deduces two axioms of a `Filter` from the countable intersection property.

## Tags
filter, countable
-/


open Set Filter

open Filter

variable {ι : Sort _} {α β : Type _}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l
#align countable_Inter_filter CountableInterFilter

variable {l : Filter α} [CountableInterFilter l]

theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩
#align countable_sInter_mem countable_sInter_mem

theorem countable_iInter_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_range_iff
#align countable_Inter_mem countable_iInter_mem

theorem countable_bInter_mem {ι : Type _} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  haveI := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall
#align countable_bInter_mem countable_bInter_mem

theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }
#align eventually_countable_forall eventually_countable_forall

theorem eventually_countable_ball {ι : Type _} {S : Set ι} (hS : S.Countable)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }
#align eventually_countable_ball eventually_countable_ball

theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 <| (mem_iUnion.1 hs).imp hst
#align eventually_le.countable_Union EventuallyLE.countable_iUnion

theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)
#align eventually_eq.countable_Union EventuallyEq.countable_iUnion

theorem EventuallyLE.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    (⋃ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  haveI := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2
#align eventually_le.countable_bUnion EventuallyLE.countable_bUnion

theorem EventuallyEq.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    (⋃ i ∈ S, s i ‹_›) =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bUnion EventuallyEq.countable_bUnion

theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)
#align eventually_le.countable_Inter EventuallyLE.countable_iInter

theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)
#align eventually_eq.countable_Inter EventuallyEq.countable_iInter

theorem EventuallyLE.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    (⋂ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  haveI := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2
#align eventually_le.countable_bInter EventuallyLE.countable_bInter

theorem EventuallyEq.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    (⋂ i ∈ S, s i ‹_›) =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bInter EventuallyEq.countable_bInter

/-- Construct a filter with countable intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α
    where
  sets := l
  univ_sets := @sInter_empty α ▸ hp _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hp _ ((countable_singleton _).insert _) (insert_subset.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter

instance Filter.countable_Inter_ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hp h_mono) :=
  ⟨hp⟩
#align filter.countable_Inter_of_countable_Inter Filter.countable_Inter_ofCountableInter

@[simp]
theorem Filter.mem_ofCountableInter {l : Set (Set α)}
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hp h_mono ↔ s ∈ l :=
  Iff.rfl
#align filter.mem_of_countable_Inter Filter.mem_ofCountableInter

instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal

instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]
  apply countableInterFilter_principal
#align countable_Inter_filter_bot countableInterFilter_bot

instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by
  rw [← principal_univ]
  apply countableInterFilter_principal
#align countable_Inter_filter_top countableInterFilter_top

instance (l : Filter β) [CountableInterFilter l] (f : α → β) :
    CountableInterFilter (comap f l) := by
  refine' ⟨fun S hSc hS => _⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  refine' ⟨_, this, _⟩
  simpa [preimage_iInter] using iInter₂_mono ht

instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) := by
  refine' ⟨fun S hSc hS => _⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS⊢
  exact (countable_bInter_mem hSc).2 hS

/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) := by
  refine' ⟨fun S hSc hS => _⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => _)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)
#align countable_Inter_filter_inf countableInterFilter_inf

/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) := by
  refine' ⟨fun S hSc hS => ⟨_, _⟩⟩ <;> refine' (countable_sInter_mem hSc).2 fun s hs => _
  exacts[(hS s hs).1, (hS s hs).2]
#align countable_Inter_filter_sup countableInterFilter_sup
