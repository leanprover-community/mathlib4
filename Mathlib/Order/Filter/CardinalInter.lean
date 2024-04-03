/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter l c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality strictly less than `c`,
their intersection belongs to `l` as well.

# Main results
* `Filter.cardinalInterFilter_aleph0` establishes that every filter `l` is a
    `CardinalInterFilter l aleph0`
* `CardinalInterFilter.toCountableInterFilter` establishes that every `CardinalInterFilter l c` with
    `c > aleph0` is a `CountableInterFilter`.
* `CountableInterFilter.toCardinalInterFilter` establishes that every `CountableInterFilter l` is a
    `CardinalInterFilter l aleph1`.
* `CardinalInterFilter.of_CardinalInterFilter_of_lt` establishes that we have
  `CardinalInterFilter l c` → `CardinalInterFilter l a` for all `a < c`.

## Tags
filter, cardinal
-/


open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u} {c : Cardinal.{u}}

/-- A filter `l` has the cardinal `c` intersection property if for any collection
of less than `c` sets `s ∈ l`, their intersection belongs to `l` as well. -/
class CardinalInterFilter (l : Filter α) (c : Cardinal.{u}) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α}

theorem cardinal_sInter_mem {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S < c) :
    ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

/-- Every filter is a CardinalInterFilter with c = aleph0 -/
theorem _root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFilter l aleph0 where
  cardinal_sInter_mem := by
    simp_all only [aleph_zero, lt_aleph0_iff_subtype_finite, setOf_mem_eq, sInter_mem,
      implies_true, forall_const]

/-- Every CardinalInterFilter with c > aleph0 is a CountableInterFilter -/
theorem CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFilter l c]
    (hc : aleph0 < c) : CountableInterFilter l where
  countable_sInter_mem := by
    intro S hS
    exact fun a ↦ CardinalInterFilter.cardinal_sInter_mem S
      (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

/-- Every CountableInterFilter is a CardinalInterFilter with c = aleph 1-/
instance CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterFilter l] :
    CardinalInterFilter l (aleph 1) where
  cardinal_sInter_mem := fun S hS a ↦ CountableInterFilter.countable_sInter_mem S
    ((countable_iff_lt_aleph_one S).mpr hS) a

theorem cardinalInterFilter_aleph_one_iff :
    CardinalInterFilter l (aleph 1) ↔ CountableInterFilter l :=
  ⟨fun _ ↦ ⟨fun S h a ↦
    CardinalInterFilter.cardinal_sInter_mem S ((countable_iff_lt_aleph_one S).1 h) a⟩,
   fun _ ↦ CountableInterFilter.toCardinalInterFilter l⟩

/-- Every CardinalInterFilter for some c also is a CardinalInterFilter for some a < c -/
theorem CardinalInterFilter.of_CardinalInterFilter_of_lt (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a < c) :
  CardinalInterFilter l a where
    cardinal_sInter_mem :=
      fun S hS a ↦ CardinalInterFilter.cardinal_sInter_mem S (lt_trans hS hac) a

namespace Filter

variable [CardinalInterFilter l c]

theorem cardinal_iInter_mem {s : ι → Set α} (hic : #ι < c) :
    (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l := by
  rw [← sInter_range _]
  apply Iff.trans
  apply cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)
  exact forall_mem_range

theorem cardinal_bInter_mem {S : Set ι} (hS : #S < c)
    {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall

theorem eventually_cardinal_forall {p : α → ι → Prop} (hic : #ι < c) :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_iInter_mem hic

theorem eventually_cardinal_ball {S : Set ι} (hS : #S < c)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simp only [Filter.Eventually, setOf_forall]
  exact cardinal_bInter_mem hS

theorem EventuallyLE.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2 <|
    (mem_iUnion.1 hs).imp hst

theorem EventuallyEq.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2

theorem EventuallyEq.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)

theorem EventuallyLE.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

theorem EventuallyEq.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)

theorem EventuallyLE.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2

theorem EventuallyEq.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

end Filter
