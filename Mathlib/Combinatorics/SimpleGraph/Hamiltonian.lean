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

In this file we introduce `Hamitonian paths`, `cylces` and `graphs`.
## Main results

- `IsHamiltonian`: the definition of `Hamitonian paths`
- `IsHamiltonianCycle`: the definition of `Hamitonian cycles`
- `IsHamiltonian`: the definition of `Hamitonian graphs`
-/

open BigOperators

namespace SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

namespace Walk

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. Note that while
this definition doesn't contain that `p` is a path, `p.isPath` gives that. -/
def IsHamiltonian (p : G.Walk u v) : Prop := ∀ v : V, p.support.count v = 1

/--
If `p` is a Hamiltonian path and `w` is a member of the vertex set of `p`, `w` is visited by `p`.
-/
lemma IsHamiltonian.mem_support {p : G.Walk u v} (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support :=
  by simp only [←List.count_pos_iff_mem, hp w]

/-- The support of a Hamiltonian walk is the entire vertex set. -/
lemma IsHamiltonian.support_toFinset {p : G.Walk u v} (hp : p.IsHamiltonian) :
    p.support.toFinset = Finset.univ :=
  Finset.eq_univ_of_forall (List.mem_toFinset.2 <| hp.mem_support ·)

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

/-- Hamiltonian paths are paths. -/
lemma IsHamiltonian.isPath {p : G.Walk u v} (hp : p.IsHamiltonian) :
    p.IsPath := IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A Hamiltonian path whose support contains every vertex is Hamiltonian. -/
lemma IsPath.isHamiltonian_of_mem {p : G.Walk u v} (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ =>
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff_mem.2 (hp' _))

lemma IsPath.isHamiltonian_iff {p : G.Walk u v} (hp : p.IsPath) :
    p.IsHamiltonian ↔ ∀ w, w ∈ p.support := ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩

/--
A *Hamiltonian cycle* is a cycle `p` that visits every vertex once.
We define this as a cycle whose tail is a Hamiltonian walk.
-/
structure IsHamiltonianCycle (p : G.Walk v v) extends p.IsCycle : Prop :=
  path_hamiltonian : (p.tail toIsCycle.not_Nil).IsHamiltonian

lemma IsHamiltonianCycle.isCycle {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    p.IsCycle := hp.toIsCycle

lemma IsHamiltonianCycle_def {p : G.Walk v v} :
    p.IsHamiltonianCycle ↔ ∃ h : p.IsCycle, (p.tail h.not_Nil).IsHamiltonian :=
⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

lemma IsHamiltonianCycle_iff {p : G.Walk v v} :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ u : V, (support p).tail.count u = 1 := by
  simp only [IsHamiltonianCycle_def, IsHamiltonian, support_tail, exists_prop]

/--
If `p` is a Hamiltonian cycle and `w` is a member of the vertex set of `p`, `w` is visited by `p`.
-/
lemma IsHamiltonianCycle.mem_support (p : G.Walk v v)
    (hp : p.IsHamiltonianCycle) (w : V) : w ∈ p.support :=
  List.mem_of_mem_tail <| support_tail _ ▸ hp.path_hamiltonian.mem_support w

/--
The length of a hamiltonian cycle is the size of the vertex set.
-/
lemma IsHamiltonianCycle.length {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card V := by
  rw [←length_tail_add_one hp.not_Nil, hp.path_hamiltonian.length, Nat.sub_add_cancel]
  rw [Nat.succ_le, Fintype.card_pos_iff]
  exact ⟨u⟩

lemma IsHamiltonianCycle.support_count {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    p.support.count v = 2 :=
  by rw [support_eq_cons, List.count_cons_self, ←support_tail, hp.path_hamiltonian v]

lemma IsHamiltonianCycle.support_count_of_ne {p : G.Walk v v} (hp : p.IsHamiltonianCycle)
    {h : u ≠ v} : p.support.count u = 1 :=
  by rw [←cons_support_tail p, List.count_cons_of_ne h, hp.path_hamiltonian u]

end Walk

/-- A *Hamiltonian graph* `G` is a *connected graph* that contains a *Hamiltonian cycle* `p`.
    By convention, the singleton graph is considered to be Hamiltonian. -/
def IsHamiltonian (G : SimpleGraph V) : Prop :=
  (G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle) ∨ Fintype.card V = 1
