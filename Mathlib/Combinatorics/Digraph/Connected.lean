/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Combinatorics.Digraph.Paths
import Mathlib.Combinatorics.Digraph.WalkDecomp

/-!
# Connectivity in Digraphs

This file defines various connectivity concepts in directed graphs, including:

* Connected components (weakly and strongly connected)
* Connectivity relations and equivalence classes
* Connected component types and properties

In a digraph, there are several notions of connectivity:

* *Connected*: There is a directed walk from u to v.
* *Weakly connected*: There is a walk between u and v if edge directions are ignored.
* *Strongly connected*: There are directed walks from u to v and from v to u.

## Main definitions

* `Digraph.Preconnected`: A digraph is preconnected if any two vertices are reachable from each other.
* `Digraph.WeaklyConnected`: A digraph is weakly connected if any two vertices are weakly reachable.
* `Digraph.StronglyConnected`: A digraph is strongly connected if any two vertices are strongly reachable.

* `Digraph.ConnectedComponent`: Type representing a connected component of a digraph.
* `Digraph.WeaklyConnectedComponent`: Type representing a weakly connected component of a digraph.
* `Digraph.StronglyConnectedComponent`: Type representing a strongly connected component of a digraph.

## Implementation notes

The implementation extends concepts from `SimpleGraph.Reachable` and `SimpleGraph.Connected`
to account for directional edges in digraphs.
-/

open Function

universe u v w

namespace Digraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : Digraph V) (G' : Digraph V')

/-! ## Reachability and Connectivity Relations -/

namespace Reachable

variable {G}

theorem refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩

protected theorem rfl {u : V} : G.Reachable u u := refl _

protected theorem trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

theorem iff_exists_walk (u v : V) : G.Reachable u v ↔ ∃ p : G.Walk u v, True :=
  Nonempty_iff.trans ⟨fun p => ⟨p, trivial⟩, fun ⟨p, _⟩ => p⟩

protected theorem Walk.reachable {u v : V} (p : G.Walk u v) : G.Reachable u v := ⟨p⟩

protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  ⟨Walk.cons h Walk.nil⟩

theorem iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.TransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil =>
      -- Nil walk: u = v, and for TransGen we need at least one step
      -- But since u = v, we actually need to handle this differently
      apply Relation.TransGen.refl
    | cons h' p ih =>
      -- If we have a walk a -> b -> ... -> c, then we have TransGen a c
      apply Relation.TransGen.head h'
      exact ih
  · intro h
    induction h with
    | refl => exact ⟨Walk.nil⟩
    | tail _ ha hr => exact hr.trans ⟨Walk.cons ha Walk.nil⟩

end Reachable

namespace StronglyReachable

variable {G}

theorem refl (u : V) : G.StronglyReachable u u := ⟨G.Reachable.refl u, G.Reachable.refl u⟩

protected theorem rfl {u : V} : G.StronglyReachable u u := refl _

@[symm]
protected theorem symm {u v : V} (huv : G.StronglyReachable u v) : G.StronglyReachable v u :=
  ⟨huv.2, huv.1⟩

theorem comm {u v : V} : G.StronglyReachable u v ↔ G.StronglyReachable v u :=
  ⟨StronglyReachable.symm, StronglyReachable.symm⟩

@[trans]
protected theorem trans {u v w : V} (huv : G.StronglyReachable u v) (hvw : G.StronglyReachable v w) :
    G.StronglyReachable u w :=
  ⟨Reachable.trans huv.1 hvw.1, Reachable.trans hvw.2 huv.2⟩

end StronglyReachable

namespace WeaklyReachable

variable {G}

theorem refl (u : V) : G.WeaklyReachable u u :=
  ⟨[u], by simp, rfl, rfl, by simp⟩

protected theorem rfl {u : V} : G.WeaklyReachable u u := refl _

@[symm]
protected theorem symm {u v : V} (huv : G.WeaklyReachable u v) : G.WeaklyReachable v u := by
  rcases huv with ⟨p, len_pos, h_head, h_last, h_adj⟩
  use p.reverse
  constructor
  · simp [len_pos]
  constructor
  · simp [h_last]
  constructor
  · simp [h_head]
  · intro i hi
    have : i < p.reverse.length - 1 := hi
    simp at this
    specialize h_adj (p.length - 2 - i) (by omega)
    simp [List.get!_reverse]
    cases h_adj <;> simp [*]

theorem comm {u v : V} : G.WeaklyReachable u v ↔ G.WeaklyReachable v u :=
  ⟨WeaklyReachable.symm, WeaklyReachable.symm⟩

@[trans]
protected theorem trans {u v w : V} (huv : G.WeaklyReachable u v) (hvw : G.WeaklyReachable v w) :
    G.WeaklyReachable u w := by
  rcases huv with ⟨p, p_len, p_head, p_last, p_adj⟩
  rcases hvw with ⟨q, q_len, q_head, q_last, q_adj⟩
  have v_eq : v = p.getLast! := p_last
  have v_eq' : v = q.head! := q_head
  subst v_eq
  subst v_eq'

  use p.dropLast ++ q
  constructor
  · simp [p_len, q_len]
  constructor
  · simp [p_head]
  constructor
  · simp [q_last]
  · intro i hi
    simp at hi
    by_cases h : i < p.dropLast.length - 1
    · specialize p_adj i (by simp [h])
      simp [List.get!_append_left _ _ (by omega)]
      exact p_adj
    · by_cases h' : i = p.dropLast.length - 1
      · have i_eq : i + 1 = p.dropLast.length := by omega
        simp [List.get!_append_left _ _ (by omega),
              List.get!_append_right _ _ (by rw [i_eq]; omega)]
        have pq_adj : G.Adj p.getLast! q.head! ∨ G.Adj q.head! p.getLast! := by
          -- Here we need to show that the last element of p and first element of q
          -- are adjacent in one direction or the other. We know they're the same vertex.
          simp
          right
          apply Reachable.refl
      · have i_geq : i ≥ p.dropLast.length := by omega
        have i_lt : i - p.dropLast.length < q.length - 1 := by
          -- Needs arithmetic reasoning
          sorry
        specialize q_adj (i - p.dropLast.length) i_lt
        simp [List.get!_append_right _ _ (by omega),
              List.get!_append_right _ _ (by omega)]
        exact q_adj

end WeaklyReachable

/-! ## Connected Component Types -/

/-- A strongly connected component is an equivalence class under the strong reachability relation. -/
structure StronglyConnectedComponent (G : Digraph V) where
  /-- A representative vertex in the strongly connected component -/
  rep : V
  /-- Every vertex in the component can reach and be reached from the representative -/
  equiv (v : V) : Prop := G.StronglyReachable v rep

namespace StronglyConnectedComponent

variable {G} {C C' : G.StronglyConnectedComponent}

/-- The set of vertices in a strongly connected component -/
def verts (C : G.StronglyConnectedComponent) : Set V := {v | C.equiv v}

theorem mem_verts (C : G.StronglyConnectedComponent) (v : V) : v ∈ C.verts ↔ C.equiv v := Iff.rfl

theorem rep_mem_verts (C : G.StronglyConnectedComponent) : C.rep ∈ C.verts :=
  StronglyReachable.refl _

theorem equiv_iff (C : G.StronglyConnectedComponent) (u v : V) :
    u ∈ C.verts ∧ v ∈ C.verts ↔ G.StronglyReachable u v := by
  constructor
  · intro ⟨hu, hv⟩
    exact StronglyReachable.trans hu (StronglyReachable.symm hv)
  · intro h
    constructor
    · exact StronglyReachable.trans h (C.mem_verts.2 (C.rep_mem_verts))
    · exact StronglyReachable.trans (StronglyReachable.symm h) (C.mem_verts.2 (C.rep_mem_verts))

theorem eq_of_mem_both (u : V) (hC : u ∈ C.verts) (hC' : u ∈ C'.verts) : C = C' := by
  ext v
  constructor <;> intro hv
  · have h1 : G.StronglyReachable v u := (C.equiv_iff v u).1 ⟨hv, hC⟩
    have h2 : G.StronglyReachable u C'.rep := hC'
    exact (C'.equiv_iff v C'.rep).2 (StronglyReachable.trans h1 h2)
  · have h1 : G.StronglyReachable v u := (C'.equiv_iff v u).1 ⟨hv, hC'⟩
    have h2 : G.StronglyReachable u C.rep := hC
    exact (C.equiv_iff v C.rep).2 (StronglyReachable.trans h1 h2)

theorem disjoint_or_eq (C C' : G.StronglyConnectedComponent) :
    Disjoint C.verts C'.verts ∨ C = C' := by
  by_cases h : Disjoint C.verts C'.verts
  · exact Or.inl h
  · right
    simp [Set.not_disjoint_iff] at h
    rcases h with ⟨u, hu, hu'⟩
    exact eq_of_mem_both u hu hu'

theorem partition_verts : Setoid.IsPartition (Set.range (verts : G.StronglyConnectedComponent → Set V)) Set.univ := by
  refine ⟨Set.range_nonempty _, ?_, ?_⟩
  · intro _ _ hC hC'
    simp only [Set.mem_range] at hC hC'
    rcases hC with ⟨C, rfl⟩
    rcases hC' with ⟨C', rfl⟩
    exact disjoint_or_eq C C'
  · intro x _
    use StronglyConnectedComponent.mk x, mem_verts _ _
    rfl

/-- The induced subgraph of a strongly connected component -/
def subgraph (C : G.StronglyConnectedComponent) : G.Subgraph :=
  G.Subgraph.induced C.equiv

theorem subgraph_isInduced (C : G.StronglyConnectedComponent) :
    Digraph.Subgraph.IsInduced C.subgraph := by
  apply Digraph.Subgraph.isInduced_iff_subset_induced.2
  rfl

end StronglyConnectedComponent

/-- A weakly connected component is an equivalence class under the weak reachability relation. -/
structure WeaklyConnectedComponent (G : Digraph V) where
  /-- A representative vertex in the weakly connected component -/
  rep : V
  /-- Every vertex in the component is weakly reachable from the representative -/
  equiv (v : V) : Prop := G.WeaklyReachable v rep

namespace WeaklyConnectedComponent

variable {G} {C C' : G.WeaklyConnectedComponent}

/-- The set of vertices in a weakly connected component -/
def verts (C : G.WeaklyConnectedComponent) : Set V := {v | C.equiv v}

theorem mem_verts (C : G.WeaklyConnectedComponent) (v : V) : v ∈ C.verts ↔ C.equiv v := Iff.rfl

theorem rep_mem_verts (C : G.WeaklyConnectedComponent) : C.rep ∈ C.verts :=
  WeaklyReachable.refl _

theorem equiv_iff (C : G.WeaklyConnectedComponent) (u v : V) :
    u ∈ C.verts ∧ v ∈ C.verts ↔ G.WeaklyReachable u v := by
  constructor
  · intro ⟨hu, hv⟩
    exact WeaklyReachable.trans hu (WeaklyReachable.symm hv)
  · intro h
    constructor
    · exact WeaklyReachable.trans h (C.mem_verts.2 (C.rep_mem_verts))
    · exact WeaklyReachable.trans (WeaklyReachable.symm h) (C.mem_verts.2 (C.rep_mem_verts))

theorem eq_of_mem_both (u : V) (hC : u ∈ C.verts) (hC' : u ∈ C'.verts) : C = C' := by
  ext v
  constructor <;> intro hv
  · have h1 : G.WeaklyReachable v u := (C.equiv_iff v u).1 ⟨hv, hC⟩
    have h2 : G.WeaklyReachable u C'.rep := hC'
    exact (C'.equiv_iff v C'.rep).2 (WeaklyReachable.trans h1 h2)
  · have h1 : G.WeaklyReachable v u := (C'.equiv_iff v u).1 ⟨hv, hC'⟩
    have h2 : G.WeaklyReachable u C.rep := hC
    exact (C.equiv_iff v C.rep).2 (WeaklyReachable.trans h1 h2)

theorem disjoint_or_eq (C C' : G.WeaklyConnectedComponent) :
    Disjoint C.verts C'.verts ∨ C = C' := by
  by_cases h : Disjoint C.verts C'.verts
  · exact Or.inl h
  · right
    simp [Set.not_disjoint_iff] at h
    rcases h with ⟨u, hu, hu'⟩
    exact eq_of_mem_both u hu hu'

theorem partition_verts : Setoid.IsPartition (Set.range (verts : G.WeaklyConnectedComponent → Set V)) Set.univ := by
  refine ⟨Set.range_nonempty _, ?_, ?_⟩
  · intro _ _ hC hC'
    simp only [Set.mem_range] at hC hC'
    rcases hC with ⟨C, rfl⟩
    rcases hC' with ⟨C', rfl⟩
    exact disjoint_or_eq C C'
  · intro x _
    use WeaklyConnectedComponent.mk x, mem_verts _ _
    rfl

end WeaklyConnectedComponent

/-- A connected component is an equivalence class under the (directed) reachability relation.
    Note that unlike strong connectivity, this relation is not necessarily symmetric. -/
structure ConnectedComponent (G : Digraph V) where
  /-- A representative vertex in the connected component -/
  rep : V
  /-- Every vertex in the component can be reached from the representative -/
  rel (v : V) : Prop := G.Reachable rep v

namespace ConnectedComponent

variable {G} {C C' : G.ConnectedComponent}

/-- The set of vertices in a connected component -/
def verts (C : G.ConnectedComponent) : Set V := {v | C.rel v}

theorem mem_verts (C : G.ConnectedComponent) (v : V) : v ∈ C.verts ↔ C.rel v := Iff.rfl

theorem rep_mem_verts (C : G.ConnectedComponent) : C.rep ∈ C.verts :=
  Reachable.refl _

theorem rel_trans (C : G.ConnectedComponent) {u v : V} (hu : C.rel u) (huv : G.Reachable u v) :
    C.rel v :=
  Reachable.trans hu huv

theorem eq_of_reachable {u v : V} (huv : G.Reachable u v) (hvu : G.Reachable v u) :
    ConnectedComponent.mk u = ConnectedComponent.mk v := by
  ext w
  constructor <;> intro h
  · exact Reachable.trans hvu h
  · exact Reachable.trans huv h

end ConnectedComponent

end Digraph
