/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Partition
import Mathlib.Order.Minimal

/-!
# Complete Multi-Partite Graphs
A graph is complete (multi)-partite iff non-adjacency is transitive.

## Main declarations
* `SimpleGraph.IsCompletePartite`: predicate for a graph to be complete-partite.
* `SimpleGraph.IsCompletePartite.setoid`: the Setoid given by non-adjacency.
* `SimpleGraph.IsCompletePartite.partition`: the Partition into independent sets

For finite vertex types:
* `SimpleGraph.IsCompletePartite.finpartition`: the Finpartition.
* `SimpleGraph.IsCompletePartite.card`: the number of parts in the Finpartition.
* `SimpleGraph.IsCompletePartite.coloring`: the coloring by parts.
* `SimpleGraph.IsP2Complement`: predicate for a witness to non-complete-partiteness of a graph,
  i.e. vertices v w₁ w₂ such that v is not adjacent to w₁ or w₂ but w₁ and w₂ are adjacent.
-/
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}

/-- G is complete-partite iff non-adjacency is transitive -/
abbrev IsCompletePartite (G : SimpleGraph α) : Prop :=
  Transitive (fun u v => ¬G.Adj u v)

namespace IsCompletePartite
variable (h: G.IsCompletePartite) include h
/-- Any induced subgraph of a complete-partite graph is complete-partite -/
lemma induced (s : Set α) : IsCompletePartite (G.induce s) :=by
  intro a b c hab hbc
  simp only [comap_adj, Function.Embedding.coe_subtype] at *
  apply h hab hbc

/-- If G is complete-partite then non-adjacency is an equivalence relation -/
lemma equivalence  : Equivalence (¬G.Adj · · ):=by
  constructor
  · exact G.loopless
  · intro _ _ h'; rwa [adj_comm] at h'
  · apply h

/-- The setoid given by non-adjacency -/
def setoid : Setoid α := ⟨_, h.equivalence⟩

/-- The partition into independent sets -/
def partition : G.Partition where
  parts := h.setoid.classes
  isPartition :=h.setoid.isPartition_classes
  independent :=by
    intro s hs x hx y hy _
    change h.setoid.r x y
    apply h.setoid.rel_iff_exists_classes.2
    use s

variable [DecidableRel G.Adj]
instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel (¬G.Adj · ·)

variable [DecidableEq α] [Fintype α]
/-- The finpartition given by non-adjacency. -/
def finpartition : Finpartition (Finset.univ : Finset α):=
  Finpartition.ofSetoid h.setoid

/-- the number of parts in a complete partite graph -/
abbrev card : ℕ := h.finpartition.parts.card

open Finset
/-- If there are any vertices then the number of parts is positive -/
lemma card_pos [Nonempty α] : 0 < h.card:= by
  simp [h.finpartition.parts_nonempty_iff,univ_eq_empty_iff]

variable {x y : α}
/-- Vertices are not adjacent iff they lie in the same part -/
lemma not_adj_iff_parts_eq :
    ¬G.Adj x y ↔ h.finpartition.part x = h.finpartition.part y := by
  change h.setoid.r x y ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change y ∈ h.finpartition.part x ↔ h.finpartition.part x = h.finpartition.part y
  rw [h.finpartition.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _), eq_comm]

/-- Vertices are adjacent iff they lie in different parts -/
lemma adj_iff_parts_ne : G.Adj x y ↔ h.finpartition.part x ≠ h.finpartition.part y:=by
  rw [← not_iff_not, not_not, h.not_adj_iff_parts_eq]

variable {t : Finset α}
/-- Any choice of vertices from distinct parts forms a clique -/
lemma injOn_isClique (ht : Set.InjOn h.finpartition.part t) : G.IsClique t:=by
  intro i hi j hj hne
  apply h.adj_iff_parts_ne.2
  intro hne1
  apply hne <| ht hi hj hne1

/-- A complete r-partite graph contains Kᵣ -/
lemma exists_isNClique_card : ∃ (s : Finset α), G.IsNClique h.card s:=by
  obtain ⟨s,hs⟩:=h.finpartition.exists_subset_part_bijOn
  use s, h.injOn_isClique hs.2.2.1, card_nbij _ hs.2.1 hs.2.2.1 hs.2.2.2

/-- If G is complete-r-partite then it is not Kᵣ-free -/
lemma not_cliqueFree  : ¬ G.CliqueFree h.card := by
  obtain ⟨s,hs⟩:=h.exists_isNClique_card
  intro hf; apply hf _ hs

variable {n : ℕ}
/-- If a complete-r-partite graph is Kₙ-free then r < n -/
lemma card_lt_of_cliqueFree (hc : G.CliqueFree n) : h.card < n :=by
  contrapose! hc
  intro hf
  apply h.not_cliqueFree <| hf.mono hc

/-- A coloring by parts-/
def coloring : G.Coloring h.finpartition.parts :=
  ⟨fun v => ⟨h.finpartition.part v, h.finpartition.part_mem (mem_univ _)⟩, fun hadj => by
    rw [top_adj,Ne, Subtype.mk_eq_mk]
    intro heq
    exact h.not_adj_iff_parts_eq.2 heq hadj⟩

/-- If G is complete r-partite it is r-colorable -/
lemma colorable : G.Colorable h.card := by
  convert h.coloring.colorable; simp

/-- A complete r-partite graph is Kₙ-free iff r < n-/
lemma cliqueFree_iff : h.card < n ↔ G.CliqueFree n :=by
  constructor <;> intro hc
  · exact h.colorable.cliqueFree hc
  · exact h.card_lt_of_cliqueFree hc

/-- A complete r-partite graph on a non-empty vertex set is not (r - 1)-colorable -/
lemma not_colorable [Nonempty α]: ¬ G.Colorable (h.card - 1) :=
    fun hc =>  h.not_cliqueFree <| hc.cliqueFree <| Nat.pred_lt_self h.card_pos

/-- The chromatic number of a complete-partite graph is the number of parts -/
lemma chromaticNumber : G.chromaticNumber = h.card := by
  apply le_antisymm h.colorable.chromaticNumber_le
  obtain ⟨s,h1,h2⟩:=h.exists_isNClique_card
  exact h2 ▸ h1.card_le_chromaticNumber

end IsCompletePartite
/--
P2Complement is the graph on 3 vertices with one edge (i.e. the complement of path of length 2).
It is a witness to non-complete-partiteness
-/
structure IsP2Complement (v w₁ w₂ : α) : Prop where
  edge : G.Adj w₁ w₂  -- w₁w₂ ∈ E(G)
  nonedge : ¬G.Adj v w₁ ∧ ¬G.Adj v w₂ -- vw₁, vw₂ ∉ E(G)

namespace IsP2Complement
variable {v w₁ w₂ : α}
lemma ne (p2 : G.IsP2Complement v w₁ w₂): v ≠ w₁ ∧ v ≠ w₂:=
    ⟨fun hvw1 => p2.nonedge.2 (hvw1.symm ▸ p2.edge),fun hvw2 => p2.nonedge.1 (hvw2 ▸ p2.edge.symm)⟩

/-- Can swap w₁ and w₂ in any IsP2Complement-/
lemma symm (h : G.IsP2Complement v w₁ w₂) : G.IsP2Complement v w₂ w₁:= by
  obtain ⟨ed,⟨n1,n2⟩⟩:=h
  exact ⟨ed.symm,⟨n2,n1⟩⟩

end IsP2Complement

/-- If G is not complete-partite then it contains an induced IsP2Complement-/
lemma IsP2Complement_of_not_completePartite (h : ¬IsCompletePartite G):
∃ v w₁ w₂, G.IsP2Complement v w₁ w₂:=by
  rw [IsCompletePartite,Transitive] at h
  push_neg at h
  obtain ⟨w₁,v,w₂,h1,h2,h3⟩:=h
  rw [adj_comm] at h1
  exact ⟨v,w₁,w₂,h3,⟨h1,h2⟩⟩

/-- Any completeMultipartite graph is complete partite-/
lemma completeMultipartiteGraph_isCompletePartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompletePartite :=by
  intro
  simp_all

/-- Any completePartite graph is isomorphic to the obvious completeMultipartiteGraph -/
def IsCompletePartite.iso (h : G.IsCompletePartite) :
  G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) => { x // h.setoid.r c.out x}) where
  toFun := fun v => ⟨⟦v⟧,⟨v, Quotient.mk_out v⟩⟩
  invFun := fun ⟨_,x⟩ =>  x.1
  left_inv := fun v => rfl
  right_inv := fun ⟨c,x⟩ => by
    ext
    · rw [Quotient.mk_eq_iff_out]
      exact h.setoid.symm x.2
    · rfl
  map_rel_iff' :=by
    simp only [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros; change ¬¬G.Adj _ _ ↔ _
    rw [not_not]

end SimpleGraph
