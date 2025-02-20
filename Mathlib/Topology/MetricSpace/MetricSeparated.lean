/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.EMetricSpace.Defs

/-!
# Metric separated pairs of sets

In this file we define the predicate `Metric.AreSeparated`. We say that two sets in an (extended)
metric space are *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is
bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/


open EMetric Set

noncomputable section

namespace Metric

/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
def AreSeparated {X : Type*} [EMetricSpace X] (s t : Set X) :=
  ∃ r, r ≠ 0 ∧ ∀ x ∈ s, ∀ y ∈ t, r ≤ edist x y

@[deprecated (since := "2025-01-21")] alias IsMetricSeparated := AreSeparated

namespace AreSeparated

variable {X : Type*} [EMetricSpace X] {s t : Set X}

@[symm]
theorem symm (h : AreSeparated s t) : AreSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩

theorem comm : AreSeparated s t ↔ AreSeparated t s := ⟨symm, symm⟩

@[simp]
theorem empty_left (s : Set X) : AreSeparated ∅ s :=
  ⟨1, one_ne_zero, fun _x => False.elim⟩

@[simp]
theorem empty_right (s : Set X) : AreSeparated s ∅ :=
  (empty_left s).symm

protected theorem disjoint (h : AreSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
  Set.disjoint_left.mpr fun x hx1 hx2 => r0 <| by simpa using hr x hx1 x hx2

theorem subset_compl_right (h : AreSeparated s t) : s ⊆ tᶜ := fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩

@[mono]
theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
    AreSeparated s' t' → AreSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩

theorem mono_left {s'} (h' : AreSeparated s' t) (hs : s ⊆ s') : AreSeparated s t :=
  h'.mono hs Subset.rfl

theorem mono_right {t'} (h' : AreSeparated s t') (ht : t ⊆ t') : AreSeparated s t :=
  h'.mono Subset.rfl ht

theorem union_left {s'} (h : AreSeparated s t) (h' : AreSeparated s' t) :
    AreSeparated (s ∪ s') t := by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)

@[simp]
theorem union_left_iff {s'} :
    AreSeparated (s ∪ s') t ↔ AreSeparated s t ∧ AreSeparated s' t :=
  ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩

theorem union_right {t'} (h : AreSeparated s t) (h' : AreSeparated s t') :
    AreSeparated s (t ∪ t') :=
  (h.symm.union_left h'.symm).symm

@[simp]
theorem union_right_iff {t'} :
    AreSeparated s (t ∪ t') ↔ AreSeparated s t ∧ AreSeparated s t' :=
  comm.trans <| union_left_iff.trans <| and_congr comm comm

theorem finite_iUnion_left_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set X}
    {t : Set X} : AreSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, AreSeparated (s i) t := by
  refine Finite.induction_on _ hI (by simp) @fun i I _ _ hI => ?_
  rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff

theorem finite_iUnion_right_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X}
    {t : ι → Set X} : AreSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, AreSeparated s (t i) := by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI

@[simp]
theorem finset_iUnion_left_iff {ι : Type*} {I : Finset ι} {s : ι → Set X} {t : Set X} :
    AreSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, AreSeparated (s i) t :=
  finite_iUnion_left_iff I.finite_toSet

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff

@[simp]
theorem finset_iUnion_right_iff {ι : Type*} {I : Finset ι} {s : Set X} {t : ι → Set X} :
    AreSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, AreSeparated s (t i) :=
  finite_iUnion_right_iff I.finite_toSet

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff

end Metric.AreSeparated
