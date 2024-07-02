/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.EMetricSpace.Basic

#align_import topology.metric_space.metric_separated from "leanprover-community/mathlib"@"57ac39bd365c2f80589a700f9fbb664d3a1a30c2"

/-!
# Metric separated pairs of sets

In this file we define the predicate `IsMetricSeparated`. We say that two sets in an (extended)
metric space are *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is
bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/


open EMetric Set

noncomputable section

/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
def IsMetricSeparated {X : Type*} [EMetricSpace X] (s t : Set X) :=
  ∃ r, r ≠ 0 ∧ ∀ x ∈ s, ∀ y ∈ t, r ≤ edist x y
#align is_metric_separated IsMetricSeparated

namespace IsMetricSeparated

variable {X : Type*} [EMetricSpace X] {s t : Set X} {x y : X}

@[symm]
theorem symm (h : IsMetricSeparated s t) : IsMetricSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩
#align is_metric_separated.symm IsMetricSeparated.symm

theorem comm : IsMetricSeparated s t ↔ IsMetricSeparated t s :=
  ⟨symm, symm⟩
#align is_metric_separated.comm IsMetricSeparated.comm

@[simp]
theorem empty_left (s : Set X) : IsMetricSeparated ∅ s :=
  ⟨1, one_ne_zero, fun _x => False.elim⟩
#align is_metric_separated.empty_left IsMetricSeparated.empty_left

@[simp]
theorem empty_right (s : Set X) : IsMetricSeparated s ∅ :=
  (empty_left s).symm
#align is_metric_separated.empty_right IsMetricSeparated.empty_right

protected theorem disjoint (h : IsMetricSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
  Set.disjoint_left.mpr fun x hx1 hx2 => r0 <| by simpa using hr x hx1 x hx2
#align is_metric_separated.disjoint IsMetricSeparated.disjoint

theorem subset_compl_right (h : IsMetricSeparated s t) : s ⊆ tᶜ := fun _ hs ht =>
  h.disjoint.le_bot ⟨hs, ht⟩
#align is_metric_separated.subset_compl_right IsMetricSeparated.subset_compl_right

@[mono]
theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
    IsMetricSeparated s' t' → IsMetricSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩
#align is_metric_separated.mono IsMetricSeparated.mono

theorem mono_left {s'} (h' : IsMetricSeparated s' t) (hs : s ⊆ s') : IsMetricSeparated s t :=
  h'.mono hs Subset.rfl
#align is_metric_separated.mono_left IsMetricSeparated.mono_left

theorem mono_right {t'} (h' : IsMetricSeparated s t') (ht : t ⊆ t') : IsMetricSeparated s t :=
  h'.mono Subset.rfl ht
#align is_metric_separated.mono_right IsMetricSeparated.mono_right

theorem union_left {s'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s' t) :
    IsMetricSeparated (s ∪ s') t := by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine ⟨min r r', ?_, fun x hx y hy => hx.elim ?_ ?_⟩
  · rw [← pos_iff_ne_zero] at r0 r0' ⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)
#align is_metric_separated.union_left IsMetricSeparated.union_left

@[simp]
theorem union_left_iff {s'} :
    IsMetricSeparated (s ∪ s') t ↔ IsMetricSeparated s t ∧ IsMetricSeparated s' t :=
  ⟨fun h => ⟨h.mono_left subset_union_left, h.mono_left subset_union_right⟩, fun h =>
    h.1.union_left h.2⟩
#align is_metric_separated.union_left_iff IsMetricSeparated.union_left_iff

theorem union_right {t'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s t') :
    IsMetricSeparated s (t ∪ t') :=
  (h.symm.union_left h'.symm).symm
#align is_metric_separated.union_right IsMetricSeparated.union_right

@[simp]
theorem union_right_iff {t'} :
    IsMetricSeparated s (t ∪ t') ↔ IsMetricSeparated s t ∧ IsMetricSeparated s t' :=
  comm.trans <| union_left_iff.trans <| and_congr comm comm
#align is_metric_separated.union_right_iff IsMetricSeparated.union_right_iff

theorem finite_iUnion_left_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set X}
    {t : Set X} : IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, IsMetricSeparated (s i) t := by
  refine Finite.induction_on hI (by simp) @fun i I _ _ hI => ?_
  rw [biUnion_insert, forall_mem_insert, union_left_iff, hI]
#align is_metric_separated.finite_Union_left_iff IsMetricSeparated.finite_iUnion_left_iff

alias ⟨_, finite_iUnion_left⟩ := finite_iUnion_left_iff
#align is_metric_separated.finite_Union_left IsMetricSeparated.finite_iUnion_left

theorem finite_iUnion_right_iff {ι : Type*} {I : Set ι} (hI : I.Finite) {s : Set X}
    {t : ι → Set X} : IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, IsMetricSeparated s (t i) := by
  simpa only [@comm _ _ s] using finite_iUnion_left_iff hI
#align is_metric_separated.finite_Union_right_iff IsMetricSeparated.finite_iUnion_right_iff

@[simp]
theorem finset_iUnion_left_iff {ι : Type*} {I : Finset ι} {s : ι → Set X} {t : Set X} :
    IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, IsMetricSeparated (s i) t :=
  finite_iUnion_left_iff I.finite_toSet
#align is_metric_separated.finset_Union_left_iff IsMetricSeparated.finset_iUnion_left_iff

alias ⟨_, finset_iUnion_left⟩ := finset_iUnion_left_iff
#align is_metric_separated.finset_Union_left IsMetricSeparated.finset_iUnion_left

@[simp]
theorem finset_iUnion_right_iff {ι : Type*} {I : Finset ι} {s : Set X} {t : ι → Set X} :
    IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, IsMetricSeparated s (t i) :=
  finite_iUnion_right_iff I.finite_toSet
#align is_metric_separated.finset_Union_right_iff IsMetricSeparated.finset_iUnion_right_iff

alias ⟨_, finset_iUnion_right⟩ := finset_iUnion_right_iff
#align is_metric_separated.finset_Union_right IsMetricSeparated.finset_iUnion_right

end IsMetricSeparated
