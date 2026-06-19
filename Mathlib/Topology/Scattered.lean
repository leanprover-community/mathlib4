/-
Copyright (c) 2026 Bhavithran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavithran
-/
module

public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset

/-!
# Scattered sets and spaces

A set is *scattered* if it contains no nonempty preperfect subset, or equivalently, if every
nonempty subset has an isolated point (relative to itself). A topological space is scattered if
its universe is a scattered set.

Scattered sets are the "opposite" of preperfect sets: a set that is both scattered and preperfect
must be empty.

## Main Definitions

* `IsScattered`: A set `s` is scattered if every nonempty subset of `s` is not preperfect.
* `ScatteredSpace`: A topological space `X` is scattered if `Set.univ` is scattered.

## Main Statements

* `isScattered_iff_forall_exists_not_accPt`: A set is scattered iff every nonempty subset has
  a point that is not an accumulation point of that subset.
* `IsScattered.subset`: Subsets of scattered sets are scattered.
* `isScattered_of_isDiscrete`: Discrete sets are scattered.
* `isScattered_iff_no_perfect`: In a T1 space, a closed set is scattered iff it contains no
  nonempty perfect subset.

## References

* https://en.wikipedia.org/wiki/Scattered_space

## Tags

scattered, perfect, isolated point, dense-in-itself
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

variable {α : Type*} [TopologicalSpace α]

/-- A set `s` is *scattered* if every nonempty subset of `s` is not preperfect, i.e., has some
point that is not an accumulation point of the subset. -/
def IsScattered (s : Set α) : Prop :=
  ∀ t ⊆ s, t.Nonempty → ¬Preperfect t

/-- A topological space is *scattered* if every nonempty subset has an isolated point. -/
@[mk_iff scatteredSpace_def]
class ScatteredSpace (α : Type*) [TopologicalSpace α] : Prop where
  univ_isScattered : IsScattered (Set.univ : Set α)

section Basic

variable {s t : Set α}

theorem isScattered_iff_forall_exists_not_accPt :
    IsScattered s ↔ ∀ t ⊆ s, t.Nonempty → ∃ x ∈ t, ¬AccPt x (𝓟 t) := by
  constructor
  · intro hs t hts ht
    by_contra! h
    exact hs t hts ht h
  · intro hs t hts ht hp
    obtain ⟨x, hx, hna⟩ := hs t hts ht
    exact hna (hp x hx)

theorem IsScattered.subset (hs : IsScattered s) (hts : t ⊆ s) : IsScattered t :=
  fun u hut hu hp ↦ hs u (hut.trans hts) hu hp

@[simp]
theorem isScattered_empty : IsScattered (∅ : Set α) :=
  fun _ hts ht _ ↦ ht.elim fun _ hx ↦ (hts hx).elim

@[simp]
theorem isScattered_singleton {a : α} : IsScattered ({a} : Set α) := by
  intro t hts ht hp
  obtain ⟨x, hx⟩ := ht
  have hacc := hp x hx
  rw [accPt_iff_nhds] at hacc
  obtain ⟨y, ⟨_, hyt⟩, hyx⟩ := hacc univ univ_mem
  exact hyx (by rw [mem_singleton_iff.mp (hts hyt), mem_singleton_iff.mp (hts hx)])

theorem IsScattered.not_preperfect_of_nonempty (hs : IsScattered s) (hne : s.Nonempty) :
    ¬Preperfect s :=
  hs s Subset.rfl hne

theorem Preperfect.not_isScattered_of_nonempty (hp : Preperfect s) (hne : s.Nonempty) :
    ¬IsScattered s :=
  fun hs ↦ hs s Subset.rfl hne hp

theorem IsScattered.eq_empty_of_preperfect (hs : IsScattered s) (hp : Preperfect s) : s = ∅ := by
  by_contra h
  exact hs s Subset.rfl (nonempty_iff_ne_empty.mpr h) hp

theorem isScattered_of_isDiscrete (hs : IsDiscrete s) : IsScattered s := by
  rw [isScattered_iff_forall_exists_not_accPt]
  intro t hts ht
  obtain ⟨x, hx⟩ := ht
  refine ⟨x, hx, ?_⟩
  intro hacc
  have hd := hs.mono hts
  rw [isDiscrete_iff_nhdsNE] at hd
  exact hacc.ne (hd x hx)

instance ScatteredSpace.of_discreteTopology [DiscreteTopology α] : ScatteredSpace α where
  univ_isScattered := isScattered_of_isDiscrete IsDiscrete.univ

theorem isScattered_iff_no_perfect [T1Space α] (hs : IsClosed s) :
    IsScattered s ↔ ∀ t ⊆ s, Perfect t → t = ∅ := by
  constructor
  · intro hsc t hts ⟨_, htp⟩
    exact (hsc.subset hts).eq_empty_of_preperfect htp
  · intro h t hts ht hp
    have hpc := hp.perfect_closure
    have hcl : closure t ⊆ s := closure_minimal hts hs
    exact (ht.mono subset_closure).ne_empty (h (closure t) hcl hpc)

end Basic

section ScatteredSpace

variable (α)

theorem ScatteredSpace.isScattered [ScatteredSpace α] (s : Set α) : IsScattered s :=
  ScatteredSpace.univ_isScattered.subset (subset_univ s)

instance ScatteredSpace.subtype [ScatteredSpace α] (s : Set α) : ScatteredSpace s := by
  constructor
  intro t _ ht hp
  have hne : (Subtype.val '' t).Nonempty := ht.image _
  have hpre : Preperfect (Subtype.val '' t) := by
    rw [preperfect_iff_subset_derivedSet] at hp ⊢
    exact (Set.image_mono hp).trans (continuous_subtype_val.image_derivedSet Subtype.val_injective)
  exact (ScatteredSpace.isScattered α _).not_preperfect_of_nonempty hne hpre

end ScatteredSpace

end
