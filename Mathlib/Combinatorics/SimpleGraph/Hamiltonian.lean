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

lemma List.toFinset_sum_count_eq {α : Type*} [DecidableEq α] {l : List α} :
    ∑ i in l.toFinset, l.count i = l.length :=
  by simpa using Multiset.toFinset_sum_count_eq (l : Multiset α)

namespace SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

namespace Walk

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def IsHamiltonian (p : G.Walk u v) : Prop := ∀ v : V, p.support.count v = 1

/--
If `p` is a Hamiltonian path and `w` is a member of the vertex set of `p`, `w` is visited by `p`.
-/
lemma IsHamiltonian.contains_vertex {p : G.Walk u v} (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support :=
  by simp only [←List.count_pos_iff_mem, hp w]

/-- The support of a Hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.support_toFinset {p : G.Walk u v} (hp : p.IsHamiltonian) :
    p.support.toFinset = Finset.univ :=
  Finset.eq_univ_of_forall (List.mem_toFinset.2 <| hp.contains_vertex ·)

/--
If `p` is a Hamiltonian path of a graph `G` its length is one less than the number of vertices of
`G`.
-/
lemma IsHamiltonian.length {p : G.Walk u v} (hp : p.IsHamiltonian) :
    p.length = Fintype.card V - 1 := by
  suffices : p.support.length = Fintype.card V
  · rw [←this, length_support, Nat.add_sub_cancel]
  have : ∑ u : V, p.support.count u = Fintype.card V
  · rw [Finset.sum_congr rfl (fun x _ => hp x), ←Finset.card_univ, Finset.card_eq_sum_ones]
  rw [←this, ←hp.support_toFinset, List.toFinset_sum_count_eq]

/--
A *Hamiltonian cycle* is a cycle `p` that visits every vertex once.
We define this as a cycle whose tail (which is a walk) is a Hamiltonian walk.
-/
structure IsHamiltonianCycle (p : G.Walk v v) extends p.IsCycle : Prop :=
  path_hamiltonian : (p.tail toIsCycle.not_Nil).IsHamiltonian

lemma IsHamiltonianCycle.isCycle {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    p.IsCycle := hp.toIsCycle

lemma IsHamiltonianCycle_def {p : G.Walk v v} :
    p.IsHamiltonianCycle ↔ ∃ h : p.IsCycle, (p.tail h.not_Nil).IsHamiltonian :=
⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

/--
If `p` is a Hamiltonian cycle and `w` is a member of the vertex set of `p`, `w` is visited by `p`.
-/
lemma IsHamiltonianCycle.contains_vertex (p : G.Walk v v)
    (hp : p.IsHamiltonianCycle) (w : V) : w ∈ p.support :=
  List.mem_of_mem_tail <| support_tail _ ▸ hp.path_hamiltonian.contains_vertex w

/--
The length of a hamiltonian cycle is the size of the vertex set.
-/
lemma IsHamiltonianCycle.length {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card V := by
  rw [←length_tail_add_one hp.isCycle.not_Nil, hp.path_hamiltonian.length, Nat.sub_add_cancel]
  rw [Nat.succ_le, Fintype.card_pos_iff]
  exact ⟨u⟩

end Walk

/-- A *Hamiltonian graph* `G` is a *connected graph* that contains a *Hamiltonian cycle* `p`.
    By convention, the singleton graph is considered to be Hamiltonian. -/
def IsHamiltonian (G : SimpleGraph V) : Prop :=
  (G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle) ∨ Fintype.card V = 1
