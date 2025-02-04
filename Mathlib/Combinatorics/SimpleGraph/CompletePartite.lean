/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Complete Multi-Partite Graphs
A graph is complete (multi)-partite iff non-adjacency is transitive.

## Main declarations
* `SimpleGraph.IsCompletePartite`: predicate for a graph to be complete-partite.
* `SimpleGraph.IsCompletePartite.setoid`: the Setoid given by non-adjacency.
* `SimpleGraph.IsCompletePartite.iso`: the graph isomorphism from G that IsCompetePartite
to the completeMultipartite graph on the quotient.
* `SimpleGraph.IsP2Complement`: predicate for 3 vertices to be a witness to not-complete-partiteness
   of a graph G
-/
universe u
namespace SimpleGraph
variable {α : Type u} {G : SimpleGraph α}

/-- G is complete-partite iff non-adjacency is transitive -/
abbrev IsCompletePartite (G : SimpleGraph α) : Prop := Transitive (¬ G.Adj · ·)

/-- The setoid given by non-adjacency -/
abbrev IsCompletePartite.setoid (h : G.IsCompletePartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless , fun h' ↦ by rwa [adj_comm] at h', fun h1 h2 ↦ h h1 h2⟩⟩

/-- Any completeMultipartite graph is complete partite-/
lemma completeMultipartiteGraph_isCompletePartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompletePartite := by
  intro
  simp_all

/-- The graph isomorphism from G to the completeMultipartite graph on its quotient -/
def IsCompletePartite.iso (h : G.IsCompletePartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) ↦ { x // h.setoid.r c.out x}) where
  toFun := fun v ↦ ⟨⟦v⟧, ⟨v, Quotient.mk_out v⟩⟩
  invFun := fun ⟨_, x⟩ ↦  x.1
  left_inv := fun v ↦ rfl
  right_inv := fun ⟨_, x⟩ ↦ by
    refine Sigma.subtype_ext ?_ rfl
    rw [Quotient.mk_eq_iff_out]
    exact h.setoid.symm x.2
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros; change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

lemma isCompletePartite_iff : G.IsCompletePartite ↔ ∃ (ι : Type u) (V : ι → Type u)
  (_ : ∀ i, Nonempty (V i)), Nonempty (G ≃g (completeMultipartiteGraph V)) := by
  constructor <;> intro h
  · refine ⟨_, _, ?_, ⟨h.iso⟩⟩
    intro i; use i.out
  · obtain ⟨_,_,_,⟨e⟩⟩ := h
    intro _ _ _ h1 h2
    rw [← e.map_rel_iff] at *
    exact (completeMultipartiteGraph_isCompletePartite _) h1 h2

section FinDecRel
variable [Fintype α] [DecidableRel G.Adj]
lemma isCompletePartite_iff_of_fintype : G.IsCompletePartite ↔ ∃ (ι : Type u)
    (_ : Fintype ι) (V : ι → Type u) (_ : ∀ i, Nonempty (V i)),
    Nonempty (G ≃g (completeMultipartiteGraph V)) := by
  constructor <;> intro h
  · have : DecidableRel h.setoid.r := inferInstanceAs <| DecidableRel (¬ G.Adj · ·)
    exact ⟨_, inferInstance, _, fun i ↦ ⟨i.out, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨ι,_,V,_,⟨e⟩⟩ := h
    exact isCompletePartite_iff.mpr ⟨ι, V, inferInstance, ⟨e⟩⟩

lemma IsCompletePartite.colorable_of_cliqueFree {n : ℕ} (h : G.IsCompletePartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) := by
  obtain ⟨ι,_,V,hn,⟨e⟩⟩ := isCompletePartite_iff_of_fintype.mp h
  exact (CompleteMultipartiteGraph.colorable_of_cliqueFree <| hc.comap e.symm).of_embedding
            e.toEmbedding

end FinDecRel
/--
P2Complement is the graph on 3 vertices with one edge (i.e. the complement of path of length 2).
It is a witness to not-complete-partiteness
-/
structure IsP2Complement (v w₁ w₂ : α) : Prop where
  edge : G.Adj w₁ w₂  -- w₁w₂ ∈ E(G)
  nonedge : ¬ G.Adj v w₁ ∧ ¬ G.Adj v w₂ -- vw₁, vw₂ ∉ E(G)

namespace IsP2Complement

variable {v w₁ w₂ : α}
lemma ne (p2 : G.IsP2Complement v w₁ w₂): v ≠ w₁ ∧ v ≠ w₂ :=
  ⟨fun hvw1 ↦ p2.nonedge.2 (hvw1.symm ▸ p2.edge),fun hvw2 ↦ p2.nonedge.1 (hvw2 ▸ p2.edge.symm)⟩

/-- Can swap w₁ and w₂ in any IsP2Complement-/
lemma symm (h : G.IsP2Complement v w₁ w₂) : G.IsP2Complement v w₂ w₁:= by
  obtain ⟨ed, ⟨n1, n2⟩⟩ := h
  exact ⟨ed.symm, ⟨n2, n1⟩⟩

end IsP2Complement

/-- If G is not complete-partite then it contains v w₁ w₂ such that
G.IsP2Complement v w₁ w₂ -/
lemma exists_isP2Complement_of_not_completePartite (h : ¬ IsCompletePartite G) :
    ∃ v w₁ w₂, G.IsP2Complement v w₁ w₂ := by
  rw [IsCompletePartite, Transitive] at h
  push_neg at h
  obtain ⟨w₁, v, w₂, h1, h2, h3⟩:=h
  rw [adj_comm] at h1
  exact ⟨v, w₁, w₂, h3, ⟨h1, h2⟩⟩

end SimpleGraph
