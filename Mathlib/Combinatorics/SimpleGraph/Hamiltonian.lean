/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.BigOperators.Basic

/-!
# Hamiltonian Graphs

In this file we introduce `Hamitonian paths`, `cylces` and `graphs`,
two main concepts in the theory of graphs.

## Main results

- `IsHamiltonian`: the definition of `Hamitonian paths`
- `IsHamiltonianCycle`: the definition of `Hamitonian cycles`
- `IsHamiltonian`: the definition of `Hamitonian graphs`
-/

open BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

/--
If `p` is a Hamiltonian path and `w` is a member of the vertex set of `p`, `w` is visited by `p`.
-/
lemma SimpleGraph.Walk.IsHamiltonian.contains_vertex (p : G.Walk u v) (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support := by simp only [←List.count_pos_iff_mem, hp w]

/--
If `p` is a Hamiltonian path of a graph `G` its length is one less than the number of vertices of
`G`.
-/
lemma SimpleGraph.Walk.IsHamiltonian.length (p : G.Walk u v) (hp : p.IsHamiltonian) :
    p.length = Fintype.card V - 1 := by
  unfold IsHamiltonian at hp
  have length_relation : p.length = p.support.length - 1
  · rw [length_support, Nat.add_sub_cancel]
  · have : p.support.length = Fintype.card V
    · have : ∑ u : V, p.support.count u = Fintype.card V
      · have : ∑ u : V, p.support.count u = ∑ u : V, 1
        · rw [Finset.sum_congr rfl]
          intro x _
          exact hp x
        · have sum_ones_eq_card : ∑ u : V, 1 = Fintype.card V
          · rw [← @Finset.card_eq_sum_ones]
            rfl
          · rwa [sum_ones_eq_card] at this
      · rw [←this]
        have h₁ := Multiset.toFinset_sum_count_eq (support p : Multiset V)
        simp only [List.toFinset_coe, Multiset.mem_coe, Multiset.coe_nodup, Multiset.coe_count,
          Multiset.coe_card, length_support] at h₁
        have h₂ : p.support.toFinset = Finset.univ
        · ext a
          constructor
          · exact fun _ ↦ Finset.mem_univ a
          · intro _
            rw [List.mem_toFinset]
            exact contains_vertex p hp a
        · rw [←h₂, h₁, length_support]
    · rwa [this] at length_relation

/-- RM: Move to Connectivity.lean-/
lemma Nil_iff_eq_nil {v : V} : ∀ {p : G.Walk v v}, p.Nil ↔ p = SimpleGraph.Walk.nil
| .nil | .cons _ _ => by simp

/-- A *Hamiltonian cycle* is a cycle `p` that visits every vertex once.-/
structure SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) extends p.IsCycle : Prop :=
  path_hamiltonian : (p.tail (ne_nil <| Nil_iff_eq_nil.1 ·)).IsHamiltonian

/-- RM: Move to Connectivity.lean-/
lemma SimpleGraph.Walk.support_of_tail_eq_tail_of_support {p : G.Walk v v} (hnil : ¬p.Nil) :
   (p.tail hnil).support = p.support.tail := by
  rw [←cons_support_tail p hnil, List.tail_cons]

lemma SimpleGraph.Walk.IsHamiltonianCycle.contains_vertex (p : G.Walk v v)
    (hp : p.IsHamiltonianCycle) (w : V) : w ∈ p.support := by
  have : w ∈ p.support.tail
  · have hnil : ¬ Nil p
    · rw [Nil_iff_eq_nil]
      apply hp.ne_nil
    · rw [←SimpleGraph.Walk.support_of_tail_eq_tail_of_support hnil]
      apply SimpleGraph.Walk.IsHamiltonian.contains_vertex (p.tail hnil) hp.path_hamiltonian w
  · exact List.mem_of_mem_tail this

lemma SimpleGraph.Walk.IsHamiltonianCycle.length (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card V := by
  have hnil : ¬p.Nil := by rw [Nil_iff_eq_nil]; apply hp.ne_nil
  rw [←SimpleGraph.Walk.length_tail_add_one hnil]
  have : (p.tail hnil).length = Fintype.card V - 1
  · apply SimpleGraph.Walk.IsHamiltonian.length
    exact hp.path_hamiltonian
  · rw [this, tsub_add_eq_add_tsub]
    · simp
    · rw [Nat.succ_le, Fintype.card_pos_iff]
      exact ⟨v⟩

/-- A *Hamiltonian graph* `G` is a *connected graph* that contains a *Hamiltonian cycle* `p`.
    By convention, the singleton graph is considered to be Hamiltonian. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  (G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle) ∨ (Fintype.card V = 1)
