/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.TrailPath

/-!
# Graph circuits and cycles

A `Circuit` in a simple graph is a nonempty trail whose first and last vertices are the same.
A `Cycle` is a circuit where all interior vertices occur only once. These are closed versions of
`Trail` and `Path` respectively.
-/

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {u v : V}

namespace Walk

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit (p : G.Walk u u) extends IsTrail p : Prop where
  ne_nil : p ≠ nil
#align simple_graph.walk.is_circuit SimpleGraph.Walk.IsCircuit
#align simple_graph.walk.is_circuit_def SimpleGraph.Walk.isCircuit_def

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsCircuit.isTrail {p : G.Walk u u} (h : IsCircuit p) : IsTrail p := h.toIsTrail
#align simple_graph.walk.is_circuit.to_trail SimpleGraph.Walk.IsCircuit.isTrail

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex is `u`
(which appears exactly twice). -/
structure IsCycle (p : G.Walk u u) extends IsCircuit p : Prop where
  support_nodup : p.support.tail.Nodup
#align simple_graph.walk.is_cycle SimpleGraph.Walk.IsCycle

-- Porting note: used to use `extends to_circuit : is_circuit p` in structure
protected lemma IsCycle.isCircuit {p : G.Walk u u} (h : p.IsCycle) : IsCircuit p := h.toIsCircuit
#align simple_graph.walk.is_cycle.to_circuit SimpleGraph.Walk.IsCycle.isCircuit

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl
#align simple_graph.walk.is_circuit_copy SimpleGraph.Walk.isCircuit_copy

theorem isCycle_def (p : G.Walk u u) : p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
#align simple_graph.walk.is_cycle_def SimpleGraph.Walk.isCycle_def

@[simp]
theorem isCycle_copy (p : G.Walk u u) (hu : u = v) : (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl
#align simple_graph.walk.is_cycle_copy SimpleGraph.Walk.isCycle_copy

@[simp]
theorem IsCycle.not_of_nil : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl
#align simple_graph.walk.is_cycle.not_of_nil SimpleGraph.Walk.IsCycle.not_of_nil

lemma IsCycle.ne_bot : ∀ {p : G.Walk u u}, p.IsCycle → G ≠ ⊥
  | nil, hp => by cases hp.ne_nil rfl
  | cons h _, hp => by rintro rfl; exact h

theorem cons_isCycle_iff (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ ¬s(u, v) ∈ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup
  tauto
#align simple_graph.walk.cons_is_cycle_iff SimpleGraph.Walk.cons_isCycle_iff

protected theorem IsCircuit.rotate [DecidableEq V] {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit := by
  refine ⟨hc.isTrail.rotate _, ?_⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simp at hn'
#align simple_graph.walk.is_circuit.rotate SimpleGraph.Walk.IsCircuit.rotate

protected theorem IsCycle.rotate [DecidableEq V] {c : G.Walk v v} (hc : c.IsCycle)
    (h : u ∈ c.support) : (c.rotate h).IsCycle := by
  refine ⟨hc.isCircuit.rotate _, ?_⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup
#align simple_graph.walk.is_cycle.rotate SimpleGraph.Walk.IsCycle.rotate

section Mapping

variable {V' : Type*} {G' : SimpleGraph V'} {f : G →g G'}

theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, map_isTrail_iff_of_injective hinj, Ne.def, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]
#align simple_graph.walk.map_is_cycle_iff_of_injective SimpleGraph.Walk.map_isCycle_iff_of_injective

alias ⟨_, map_isCycle_of_injective⟩ := map_isCycle_iff_of_injective
#align simple_graph.walk.map_is_cycle_of_injective SimpleGraph.Walk.map_isCycle_of_injective

@[simp]
theorem mapLe_isCycle (h : G ≤ H) {p : G.Walk u u} : (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_cycle SimpleGraph.Walk.mapLe_isCycle

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := mapLe_isCycle
#align simple_graph.walk.is_cycle.of_map_le SimpleGraph.Walk.IsCycle.of_mapLe
#align simple_graph.walk.is_cycle.map_le SimpleGraph.Walk.IsCycle.mapLe

end Mapping

protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.find?, List.mem_cons, forall_eq_or_imp, mem_edgeSet] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩
#align simple_graph.walk.is_cycle.transfer SimpleGraph.Walk.IsCycle.transfer

protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _
#align simple_graph.walk.is_cycle.to_delete_edges SimpleGraph.Walk.IsCycle.toDeleteEdges

end Walk

namespace Path

theorem cons_isCycle (p : G.Path v u) (h : G.Adj u v)
    (he : ¬s(u, v) ∈ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.cons_isTrail_iff, he]
#align simple_graph.path.cons_is_cycle SimpleGraph.Path.cons_isCycle

end Path

end SimpleGraph
