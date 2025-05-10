/-
Copyright (c) 2025 Yunge Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunge Yu
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Trails

/-!

# Singleton Graphs

This module introduces *singleton graphs*.

## Main definitions

* `SimpleGraph.Singleton` is a predicate for a graph being a singleton graph

## Tags

singleton graphs
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

variable [Fintype V]

/-- A graph is a *singleton* if it only has one vertex. -/
def Singleton : Prop := 1 = Fintype.card V

namespace Singleton

lemma one_elem (s : @Singleton V _) : ∃ (v : V), (Finset.univ : Finset V) = {v} := by
  unfold Singleton at s
  simp only [<- Finset.card_univ, eq_comm] at s
  exact Finset.card_eq_one.mp s

lemma all_elem_eq (s : @Singleton V _) (u v : V) : u = v := by
  unfold Singleton at s
  have : (Finset.univ : Finset V).card ≤ 1 := by simp [s]
  apply ((Finset.univ : Finset V).card_le_one).mp this u (Finset.mem_univ u) v (Finset.mem_univ v)

lemma Connected (s : @Singleton V _) : G.Connected := by
  have : Nonempty V := by
    unfold Singleton at s
    rw [← Fintype.card_pos_iff]
    simp [<- s]
  simp only [connected_iff, this, and_true, Preconnected]
  intro u v
  have : u = v := by apply s.all_elem_eq
  simp [this, Reachable.refl]

lemma no_edges (s : @Singleton V _) : G.edgeSet = ∅ := by
  by_contra h
  simp only [Set.eq_empty_iff_forall_not_mem, not_forall, not_not] at h
  obtain ⟨⟨u, v⟩, he⟩ := h
  simp only [mem_edgeSet] at he
  have : u = v := by apply s.all_elem_eq
  simp [this] at he

variable [DecidableEq V]

theorem IsEulerian (s : @Singleton V _) : ∃ (v : V) (p : G.Walk v v), p.IsEulerian := by
  obtain ⟨v, _⟩ := s.one_elem
  use v
  use Walk.nil
  simp [Walk.isEulerian_iff, s.no_edges]

lemma IsHamiltonian (s : @Singleton V _) : G.IsHamiltonian := by
  unfold SimpleGraph.IsHamiltonian
  unfold Singleton at s
  simp [s]

end Singleton

end SimpleGraph
