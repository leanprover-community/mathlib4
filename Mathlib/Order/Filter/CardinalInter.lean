/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality at most `c`, their intersection
belongs to `l` as well.

For `c = aleph0`, this property is satisfied by all filters.
For `c = aleph1`, this agrees (to be shown!) with the CountableInterFilter.

Most results from CountableInterFilter generalise in a straightforward way.

## Tags
filter, cardinal
-/


open Set Filter

open Filter

universe u
variable {ι : Type u} {α β : Type u} {c : Cardinal.{u}}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CardinalInterFilter (l : Filter α) (hc : Cardinal.aleph0 ≤ c) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : ∀ S : Set (Set α), (Cardinal.mk S < c) → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α} {hc : Cardinal.aleph0 ≤ c} [CardinalInterFilter l hc]

theorem cardinal_sInter_mem {S : Set (Set α)} (hSc : Cardinal.mk S < c) :
    ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ _ hSc⟩

theorem cardinal_iInter_mem {s : ι → Set α} (hic : Cardinal.mk ι < c) :
    (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l := by
  rw [← sInter_range _]
  apply Iff.trans
  apply cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)
  exact forall_range_iff

theorem cardinal_bInter_mem {S : Set ι} (hS : Cardinal.mk S < c)
    {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

theorem eventually_cardinal_forall {p : α → ι → Prop} (hic : Cardinal.mk ι < c) :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_iInter_mem hic

theorem eventually_cardinal_ball {S : Set ι} (hS : Cardinal.mk S < c)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_bInter_mem hS

theorem EventuallyLE.cardinal_iUnion {s t : ι → Set α} (hic : Cardinal.mk ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2 <|
    (mem_iUnion.1 hs).imp hst

theorem EventuallyEq.cardinal_iUnion {s t : ι → Set α} (hic : Cardinal.mk ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bUnion {S : Set ι} (hS : Cardinal.mk S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

theorem EventuallyEq.cardinal_bUnion {S : Set ι} (hS : Cardinal.mk S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

theorem EventuallyLE.cardinal_iInter {s t : ι → Set α} (hic : Cardinal.mk ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

theorem EventuallyEq.cardinal_iInter {s t : ι → Set α} (hic : Cardinal.mk ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bInter {S : Set ι} (hS : Cardinal.mk S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

theorem EventuallyEq.cardinal_bInter {S : Set ι} (hS : Cardinal.mk S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)
