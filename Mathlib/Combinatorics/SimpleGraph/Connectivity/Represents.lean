/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card

/-!
# Represtation of components by a set of vertices

## Main definition

* `Set.Represents` says that a set of vertices represents a set of components if it contains exactly
  one vertex from each component.
-/

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace SimpleGraph

namespace ConnectedComponent

/-- A set of vertices represents a set of components if it contains exactly
one vertex from each component.
-/
structure _root_.Set.Represents (s : Set V) (C : Set G.ConnectedComponent) where
  unique_rep {c : G.ConnectedComponent} (h : c ∈ C) : ∃! v, v ∈ s ∩ c.supp
  exact {c : G.ConnectedComponent} (h : c ∉ C) : s ∩ c.supp = ∅

lemma represents_of_image_exists_rep_choose (C : Set G.ConnectedComponent) :
    ((fun c ↦ c.out) '' C).Represents C where
  unique_rep {c} h := by
    use c.out
    simp only [Set.mem_inter_iff, mem_supp_iff, and_imp]
    refine ⟨⟨by aesop, Quot.out_eq _⟩, ?_⟩
    intro y hy hyc
    obtain ⟨c', ⟨_, rfl⟩⟩ := hy
    rw [← hyc, show G.connectedComponentMk (Quot.out c') = c'
      from Quot.out_eq c']
  exact {c} {h} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_image, mem_supp_iff, Set.mem_empty_iff_false, iff_false,
      not_and, forall_exists_index, and_imp]
    intro c' hc' hv hvc
    have : c = c' := by
      rw [← hvc, ← hv]
      exact (Quot.exists_rep c').choose_spec
    exact h (this ▸ hc')

lemma ncard_represents_inter_supp {C : Set G.ConnectedComponent} {s : Set V}
    {c : G.ConnectedComponent} (hrep : s.Represents C) (h : c ∈ C) : (s ∩ c.supp).ncard = 1 := by
  rw [Set.ncard_eq_one]
  obtain ⟨a, ha⟩ := hrep.unique_rep h
  aesop

lemma disjoint_represents_supp {C : Set G.ConnectedComponent} {s : Set V}
    {c : G.ConnectedComponent} (hrep : s.Represents C) (h : c ∉ C) : Disjoint s c.supp := by
  rw [Set.disjoint_right]
  intro v hv hvr
  have := hrep.exact h
  rw [Set.eq_empty_iff_forall_not_mem] at this
  simp_all

lemma disjoint_supp_of_represents {c : G.ConnectedComponent}
    {s : Set V} {p : G.ConnectedComponent → Prop}
    (hrep : s.Represents {c | p c})
    (h : ¬ p c) : Disjoint s c.supp := by
  apply disjoint_represents_supp hrep
  simp_all only [Set.mem_setOf_eq, not_false_eq_true]

lemma ncard_supp_sdiff_represents_of_mem [Fintype V] {c : G.ConnectedComponent}
    {s : Set V} {C : Set (G.ConnectedComponent)}
    (hrep : s.Represents C) (h : c ∈ C) : (c.supp \ s).ncard = c.supp.ncard - 1 := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c.supp s (Set.toFinite _),
    Set.inter_comm, ncard_represents_inter_supp hrep h]

lemma ncard_supp_sdiff_represents_of_not_mem [Fintype V] {c : G.ConnectedComponent}
    {s : Set V} {C : Set (G.ConnectedComponent)}
    (hrep : s.Represents C) (h : c ∉ C) : (c.supp \ s).ncard = c.supp.ncard := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c.supp s (Set.toFinite _),
    Set.inter_comm, hrep.exact h]

end ConnectedComponent

end SimpleGraph
