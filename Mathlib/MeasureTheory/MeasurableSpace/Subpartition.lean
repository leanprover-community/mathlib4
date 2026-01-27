/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.OmegaCompletePartialOrder
/-!
# Subpartitions

Instead of working with partitions of a set `s`, we work with "subpartitions", finite sets of
disjoint sets contained within `s` since the same value will be achieved in the supremum. The empty
set is forbidden so that subpartitions of disjoint sets are disjoint sets of sets.
-/

@[expose] public section

open Function

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- A Subpartition is a finite collection of pairwise disjoint measurable sets which are all
contained within a given set. Different to `Setoid.IsPartition` there is no requirement for the
union to be the entire set and the the number of partition elements is required to be finite.
-/
structure IsSubpartition (s : Set X) (P : Finset (Set X)) where
  /-- Each partition element is contained within the ambient set -/
  subset : ∀ t ∈ P, t ⊆ s
  /-- Each partition element are measurable -/
  measurableSet : ∀ t ∈ P, MeasurableSet t
  /-- The partition elements are pairwise disjoint -/
  disjoint : (P : Set (Set X)).PairwiseDisjoint id
  /-- No partition element is the empty set -/
  nonempty : ∀ p ∈ P, p.Nonempty

namespace IsSubpartition

/-- A Subpartition of `∅` is empty. -/
lemma eq_empty {P : Finset (Set X)} (hP : IsSubpartition ∅ P) : P = ∅ := by
  obtain ⟨h, _, _, h'⟩ := hP
  refine Finset.eq_empty_of_forall_notMem ?_
  by_contra! hc
  obtain ⟨p, hp⟩ := hc
  exact (h' p hp).ne_empty (Set.subset_eq_empty (h p hp) rfl)

/-- If `P` is a Subpartition of `s₁` satisfying `p` and if `s₁ ⊆ s₂`, then `P` is a Subpartition of
`s₂`. -/
lemma mono {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (P : Finset (Set X)) (hP : IsSubpartition s₁ P) :
    IsSubpartition s₂ P := by
  obtain ⟨h1, h2, h3, _⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, by simp_all⟩

open Classical in
/-- If the `s i` are pairwise disjoint sets and each `P i` is a subpartition of `s i` then the union
of finitely many of the `P i` is a subpartition of `⋃ i, s i`. -/
lemma iUnion {ι : Type*} {s : ι → Set X} (hs : Pairwise (Disjoint on s))
    {P : ι → Finset (Set X)} (hP : ∀ i, IsSubpartition (s i) (P i)) (A : Finset ι) :
    IsSubpartition (⋃ i, s i) (Finset.biUnion A P) := by
  refine ⟨fun u hu x hp ↦ ?_, fun t ht ↦ ?_, fun t ht q hq hpq _ hrp hrq ↦ ?_, fun u hu ↦ ?_⟩
  · simp only [Finset.mem_biUnion] at hu
    obtain ⟨i, hi⟩ := hu
    rw [Set.mem_iUnion]
    use i
    exact (hP i).subset u hi.2 hp
  · obtain ⟨i, hi, hp⟩ : ∃ i ∈ A, t ∈ P i := by simp_all
    exact (hP i).measurableSet t hp
  · obtain ⟨i, hi, hp⟩ : ∃ i ∈ A, t ∈ P i := by simp_all
    obtain ⟨j, hj, hq⟩ : ∃ i ∈ A, q ∈ P i := by simp_all
    obtain hc | hc : i = j ∨ i ≠ j := Decidable.eq_or_ne i j
    · rw [hc] at hp
      simpa using Set.subset_eq_empty ((hP j).disjoint hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).subset t hp
      have hq' := (hP j).subset q hq
      simpa using Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · obtain ⟨i, hi, ht'⟩ : ∃ i ∈ A, u ∈ P i := by simp_all
    exact ((hP i).nonempty) u ht'

/-- If `P`, `Q` are subpartitions of two disjoint sets then `P` and `Q` are disjoint. -/
lemma disjoint_of_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : IsSubpartition s P) (hQ : IsSubpartition t Q) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc.ne_empty
  have := hst (hP.subset r <| hRP hr) (hQ.subset r <| hRQ hr)
  have hc := Set.subset_eq_empty this rfl
  have := hP.nonempty r (hRP hr)
  simp_all

open Classical in
/-- The restriction of a subpartition `P` to the set `t`. -/
noncomputable def restriction (t : Set X) (P : Finset (Set X)) : Finset (Set X) :=
  (P.image (fun p ↦ p ∩ t)).filter Set.Nonempty

/-- If `P` is a subpartition then the restriction of `P` to a set `t` is a subpartition of `t`. -/
lemma restriction_of_measurableSet {s t : Set X} {P : Finset (Set X)} (hs : IsSubpartition s P)
    (ht : MeasurableSet t) : IsSubpartition t (restriction t P) := by
  classical
  refine ⟨fun _ h ↦ ?_, fun r hr ↦ ?_, fun _ hr _ hr' ↦ ?_, fun _ hp ↦ ?_⟩
  · obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    simpa [← hp'] using MeasurableSet.inter (hs.measurableSet p hp) ht
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt _ h h'
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    exact hs.disjoint hp hq hpq (Set.subset_inter_iff.mp h).1 (Set.subset_inter_iff.mp h').1
  · refine Set.nonempty_coe_sort.mp ?_
    have := (Finset.mem_filter.mp hp).2
    exact Set.Nonempty.to_subtype this

end IsSubpartition

end MeasureTheory
