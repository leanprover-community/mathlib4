/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe

! This file was ported from Lean 3 source module combinatorics.simple_graph.basic
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rel
import Mathbin.Data.Set.Finite
import Mathbin.Data.Sym.Sym2

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `simple_graph.neighbor_set` is the `set` of vertices adjacent to a given vertex

* `simple_graph.common_neighbors` is the intersection of the neighbor sets of two given vertices

* `simple_graph.neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `simple_graph.incidence_set` is the `set` of edges containing a given vertex

* `simple_graph.incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

* `simple_graph.dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

* `simple_graph.hom`, `simple_graph.embedding`, and `simple_graph.iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `boolean_algebra` instance: Under the subgraph relation, `simple_graph` forms a `boolean_algebra`.
  In other words, this is the lattice of spanning subgraphs of the complete graph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

## Implementation notes

* A locally finite graph is one with instances `Π v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `rel_hom`, `rel_embedding`, and `rel_iso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

## Todo

* Upgrade `simple_graph.boolean_algebra` to a `complete_boolean_algebra`.

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/


open Finset Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric adj := by obviously
  loopless : Irreflexive adj := by obviously
#align simple_graph SimpleGraph

noncomputable instance {V : Type u} [Fintype V] : Fintype (SimpleGraph V) := by
  classical exact Fintype.ofInjective SimpleGraph.Adj SimpleGraph.ext

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V
    where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
  symm := fun a b ⟨hn, hr⟩ => ⟨hn.symm, hr.symm⟩
  loopless := fun a ⟨hn, _⟩ => hn rfl
#align simple_graph.from_rel SimpleGraph.fromRel

@[simp]
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl
#align simple_graph.from_rel_adj SimpleGraph.fromRel_adj

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `mathlib`, this is usually referred to as `⊤`. -/
def completeGraph (V : Type u) : SimpleGraph V where Adj := Ne
#align complete_graph completeGraph

/-- The graph with no edges on a given vertex type `V`. `mathlib` prefers the notation `⊥`. -/
def emptyGraph (V : Type u) : SimpleGraph V where Adj i j := False
#align empty_graph emptyGraph

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def completeBipartiteGraph (V W : Type _) : SimpleGraph (Sum V W)
    where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm := by
    intro v w
    cases v <;> cases w <;> simp
  loopless := by
    intro v
    cases v <;> simp
#align complete_bipartite_graph completeBipartiteGraph

namespace SimpleGraph

variable {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : SimpleGraph V)
  (G' : SimpleGraph W) {a b c u v w : V} {e : Sym2 V}

@[simp]
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless v
#align simple_graph.irrefl SimpleGraph.irrefl

theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  ⟨fun x => G.symm x, fun x => G.symm x⟩
#align simple_graph.adj_comm SimpleGraph.adj_comm

@[symm]
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm h
#align simple_graph.adj_symm SimpleGraph.adj_symm

theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h
#align simple_graph.adj.symm SimpleGraph.Adj.symm

theorem ne_of_adj (h : G.Adj a b) : a ≠ b :=
  by
  rintro rfl
  exact G.irrefl h
#align simple_graph.ne_of_adj SimpleGraph.ne_of_adj

protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h
#align simple_graph.adj.ne SimpleGraph.Adj.ne

protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.Ne.symm
#align simple_graph.adj.ne' SimpleGraph.Adj.ne'

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)
#align simple_graph.ne_of_adj_of_not_adj SimpleGraph.ne_of_adj_of_not_adj

section Order

/-- The relation that one `simple_graph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
#align simple_graph.is_subgraph SimpleGraph.IsSubgraph

instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : SimpleGraph V → SimpleGraph V → Prop) = (· ≤ ·) :=
  rfl
#align simple_graph.is_subgraph_eq_le SimpleGraph.isSubgraph_eq_le

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : HasSup (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj ⊔ y.Adj
      symm := fun v w h => by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl
#align simple_graph.sup_adj SimpleGraph.sup_adj

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : HasInf (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj ⊓ y.Adj
      symm := fun v w h => by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl
#align simple_graph.inf_adj SimpleGraph.inf_adj

/-- We define `Gᶜ` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves).
-/
instance : HasCompl (SimpleGraph V) :=
  ⟨fun G =>
    { Adj := fun v w => v ≠ w ∧ ¬G.Adj v w
      symm := fun v w ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩
      loopless := fun v ⟨hne, _⟩ => (hne rfl).elim }⟩

@[simp]
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w :=
  Iff.rfl
#align simple_graph.compl_adj SimpleGraph.compl_adj

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : SDiff (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj \ y.Adj
      symm := fun v w h => by change x.adj w v ∧ ¬y.adj w v <;> rwa [x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl
#align simple_graph.sdiff_adj SimpleGraph.sdiff_adj

instance : BooleanAlgebra (SimpleGraph V) :=
  { PartialOrder.lift Adj ext with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w h => x.ne_of_adj h
    bot_le := fun x v w h => h.elim
    sup_le := fun x y z hxy hyz v w h => h.casesOn (fun h => hxy h) fun h => hyz h
    sdiff_eq := fun x y => by
      ext (v w)
      refine' ⟨fun h => ⟨h.1, ⟨_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rintro rfl
      exact x.irrefl h.1
    le_sup_left := fun x y v w h => Or.inl h
    le_sup_right := fun x y v w h => Or.inr h
    le_inf := fun x y z hxy hyz v w h => ⟨hxy h, hyz h⟩
    le_sup_inf := fun a b c v w h =>
      Or.dcases_on h.2 Or.inl <| Or.dcases_on h.1 (fun h _ => Or.inl h) fun hb hc => Or.inr ⟨hb, hc⟩
    inf_compl_le_bot := fun a v w h => False.elim <| h.2.2 h.1
    top_le_sup_compl := fun a v w ne => by
      by_cases a.adj v w
      exact Or.inl h
      exact Or.inr ⟨Ne, h⟩
    inf_le_left := fun x y v w h => h.1
    inf_le_right := fun x y v w h => h.2 }

@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
#align simple_graph.top_adj SimpleGraph.top_adj

@[simp]
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl
#align simple_graph.bot_adj SimpleGraph.bot_adj

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl
#align simple_graph.complete_graph_eq_top SimpleGraph.completeGraph_eq_top

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl
#align simple_graph.empty_graph_eq_bot SimpleGraph.emptyGraph_eq_bot

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj := fun v w => Decidable.false
#align simple_graph.bot.adj_decidable SimpleGraph.Bot.adjDecidable

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj := fun v w => Or.decidable
#align simple_graph.sup.adj_decidable SimpleGraph.Sup.adjDecidable

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj := fun v w => And.decidable
#align simple_graph.inf.adj_decidable SimpleGraph.Inf.adjDecidable

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj := fun v w => And.decidable
#align simple_graph.sdiff.adj_decidable SimpleGraph.Sdiff.adjDecidable

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj := fun v w => Not.decidable
#align simple_graph.top.adj_decidable SimpleGraph.Top.adjDecidable

instance Compl.adjDecidable : DecidableRel Gᶜ.Adj := fun v w => And.decidable
#align simple_graph.compl.adj_decidable SimpleGraph.Compl.adjDecidable

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V :=
  Rel.dom G.Adj
#align simple_graph.support SimpleGraph.support

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_support SimpleGraph.mem_support

theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  Rel.dom_mono h
#align simple_graph.support_mono SimpleGraph.support_mono

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighborSet (v : V) : Set V :=
  setOf (G.Adj v)
#align simple_graph.neighbor_set SimpleGraph.neighborSet

instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  by
  unfold neighbor_set
  infer_instance
#align simple_graph.neighbor_set.mem_decidable SimpleGraph.neighborSet.memDecidable

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj v w`.)
-/
def edgeSet : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLeIff (fun G => Sym2.fromRel G.symm) fun G G' =>
    ⟨fun h a b => @h ⟦(a, b)⟧, fun h e => Sym2.ind (@h) e⟩
#align simple_graph.edge_set SimpleGraph.edgeSet

@[simp]
theorem mem_edgeSet : ⟦(v, w)⟧ ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_edge_set SimpleGraph.mem_edgeSet

theorem not_isDiag_of_mem_edgeSet : e ∈ G.edgeSet → ¬e.IsDiag :=
  Sym2.ind (fun v w => Adj.ne) e
#align simple_graph.not_is_diag_of_mem_edge_set SimpleGraph.not_isDiag_of_mem_edgeSet

@[simp]
theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ :=
  (edgeSet : SimpleGraph V ↪o Set (Sym2 V)).eq_iff_eq
#align simple_graph.edge_set_inj SimpleGraph.edgeSet_inj

@[simp]
theorem edgeSet_subset_edgeSet : G₁.edgeSet ⊆ G₂.edgeSet ↔ G₁ ≤ G₂ :=
  (edgeSet : SimpleGraph V ↪o Set (Sym2 V)).le_iff_le
#align simple_graph.edge_set_subset_edge_set SimpleGraph.edgeSet_subset_edgeSet

@[simp]
theorem edgeSet_sSubset_edgeSet : G₁.edgeSet ⊂ G₂.edgeSet ↔ G₁ < G₂ :=
  (edgeSet : SimpleGraph V ↪o Set (Sym2 V)).lt_iff_lt
#align simple_graph.edge_set_ssubset_edge_set SimpleGraph.edgeSet_sSubset_edgeSet

theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  edgeSet.Injective
#align simple_graph.edge_set_injective SimpleGraph.edgeSet_injective

alias edge_set_subset_edge_set ↔ _ edge_set_mono
#align simple_graph.edge_set_mono SimpleGraph.edgeSet_mono

alias edge_set_ssubset_edge_set ↔ _ edge_set_strict_mono
#align simple_graph.edge_set_strict_mono SimpleGraph.edgeSet_strict_mono

attribute [mono] edge_set_mono edge_set_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot
#align simple_graph.edge_set_bot SimpleGraph.edgeSet_bot

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet :=
  by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_sup SimpleGraph.edgeSet_sup

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet :=
  by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_inf SimpleGraph.edgeSet_inf

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet :=
  by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_sdiff SimpleGraph.edgeSet_sdiff

/-- This lemma, combined with `edge_set_sdiff` and `edge_set_from_edge_set`,
allows proving `(G \ from_edge_set s).edge_set = G.edge_set \ s` by `simp`.
-/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ { e | e.IsDiag }) = G.edgeSet \ s :=
  by
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not, and_congr_right_iff]
  intro h
  simp only [G.not_is_diag_of_mem_edge_set h, imp_false]
#align simple_graph.edge_set_sdiff_sdiff_is_diag SimpleGraph.edgeSet_sdiff_sdiff_isDiag

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e :=
  by
  refine' ⟨fun _ => ⟨G.ne_of_adj ‹_›, ⟦(v, w)⟧, _⟩, _⟩
  · simpa
  · rintro ⟨hne, e, he, hv⟩
    rw [Sym2.mem_and_mem_iff hne] at hv
    subst e
    rwa [mem_edge_set] at he
#align simple_graph.adj_iff_exists_edge SimpleGraph.adj_iff_exists_edge

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, ↑e = ⟦(a, b)⟧ := by
  simp only [mem_edge_set, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]
#align simple_graph.adj_iff_exists_edge_coe SimpleGraph.adj_iff_exists_edge_coe

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) : h.other ≠ v :=
  by
  erw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he
#align simple_graph.edge_other_ne SimpleGraph.edge_other_ne

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred _
#align simple_graph.decidable_mem_edge_set SimpleGraph.decidableMemEdgeSet

instance fintypeEdgeSet [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _
#align simple_graph.fintype_edge_set SimpleGraph.fintypeEdgeSet

instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet :=
  by
  rw [edge_set_bot]
  infer_instance
#align simple_graph.fintype_edge_set_bot SimpleGraph.fintypeEdgeSetBot

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edge_set_sup]
  infer_instance
#align simple_graph.fintype_edge_set_sup SimpleGraph.fintypeEdgeSetSup

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edge_set_inf]
  exact Set.fintypeInter _ _
#align simple_graph.fintype_edge_set_inf SimpleGraph.fintypeEdgeSetInf

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edge_set_sdiff]
  exact Set.fintypeDiff _ _
#align simple_graph.fintype_edge_set_sdiff SimpleGraph.fintypeEdgeSetSdiff

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/-- `from_edge_set` constructs a `simple_graph` from a set of edges, without loops.
-/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm v w h := ⟨Sym2.toRel_symmetric s h.1, h.2.symm⟩
#align simple_graph.from_edge_set SimpleGraph.fromEdgeSet

@[simp]
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ ⟦(v, w)⟧ ∈ s ∧ v ≠ w :=
  Iff.rfl
#align simple_graph.from_edge_set_adj SimpleGraph.fromEdgeSet_adj

-- Note: we need to make sure `from_edge_set_adj` and this lemma are confluent.
-- In particular, both yield `⟦(u, v)⟧ ∈ (from_edge_set s).edge_set` ==> `⟦(v, w)⟧ ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } :=
  by
  ext e
  exact Sym2.ind (by simp) e
#align simple_graph.edge_set_from_edge_set SimpleGraph.edgeSet_fromEdgeSet

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G :=
  by
  ext (v w)
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩
#align simple_graph.from_edge_set_edge_set SimpleGraph.fromEdgeSet_edgeSet

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ :=
  by
  ext (v w)
  simp only [from_edge_set_adj, Set.mem_empty_iff_false, false_and_iff, bot_adj]
#align simple_graph.from_edge_set_empty SimpleGraph.fromEdgeSet_empty

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ :=
  by
  ext (v w)
  simp only [from_edge_set_adj, Set.mem_univ, true_and_iff, top_adj]
#align simple_graph.from_edge_set_univ SimpleGraph.fromEdgeSet_univ

@[simp]
theorem fromEdgeSet_inf (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊓ fromEdgeSet t = fromEdgeSet (s ∩ t) :=
  by
  ext (v w)
  simp only [from_edge_set_adj, Set.mem_inter_iff, Ne.def, inf_adj]
  tauto
#align simple_graph.from_edge_set_inf SimpleGraph.fromEdgeSet_inf

@[simp]
theorem fromEdgeSet_sup (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊔ fromEdgeSet t = fromEdgeSet (s ∪ t) :=
  by
  ext (v w)
  simp [Set.mem_union, or_and_right]
#align simple_graph.from_edge_set_sup SimpleGraph.fromEdgeSet_sup

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet s \ fromEdgeSet t = fromEdgeSet (s \ t) :=
  by
  ext (v w)
  constructor <;> simp (config := { contextual := true })
#align simple_graph.from_edge_set_sdiff SimpleGraph.fromEdgeSet_sdiff

@[mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t :=
  by
  rintro v w
  simp (config := { contextual := true }) only [from_edge_set_adj, Ne.def, not_false_iff,
    and_true_iff, and_imp]
  exact fun vws _ => h vws
#align simple_graph.from_edge_set_mono SimpleGraph.fromEdgeSet_mono

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet :=
  by
  rw [edge_set_from_edge_set s]
  infer_instance

end FromEdgeSet

/-! ## Darts -/


/-- A `dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
@[ext]
structure Dart extends V × V where
  is_adj : G.Adj fst snd
  deriving DecidableEq
#align simple_graph.dart SimpleGraph.Dart

section Darts

variable {G}

/-- The first vertex for the dart. -/
abbrev Dart.fst (d : G.Dart) : V :=
  d.fst
#align simple_graph.dart.fst SimpleGraph.Dart.fst

/-- The second vertex for the dart. -/
abbrev Dart.snd (d : G.Dart) : V :=
  d.snd
#align simple_graph.dart.snd SimpleGraph.Dart.snd

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  dart.ext
#align simple_graph.dart.to_prod_injective SimpleGraph.Dart.toProd_injective

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σv, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩
      left_inv := fun s => by ext <;> simp
      right_inv := fun d => by ext <;> simp }
#align simple_graph.dart.fintype SimpleGraph.Dart.fintype

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  ⟦d.toProd⟧
#align simple_graph.dart.edge SimpleGraph.Dart.edge

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = ⟦p⟧ :=
  rfl
#align simple_graph.dart.edge_mk SimpleGraph.Dart.edge_mk

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.edgeSet :=
  d.is_adj
#align simple_graph.dart.edge_mem SimpleGraph.Dart.edge_mem

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, G.symm d.is_adj⟩
#align simple_graph.dart.symm SimpleGraph.Dart.symm

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl
#align simple_graph.dart.symm_mk SimpleGraph.Dart.symm_mk

@[simp]
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.mk'_prod_swap_eq
#align simple_graph.dart.edge_symm SimpleGraph.Dart.edge_symm

@[simp]
theorem Dart.edge_comp_symm : dart.edge ∘ dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm
#align simple_graph.dart.edge_comp_symm SimpleGraph.Dart.edge_comp_symm

@[simp]
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _
#align simple_graph.dart.symm_symm SimpleGraph.Dart.symm_symm

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  dart.symm_symm
#align simple_graph.dart.symm_involutive SimpleGraph.Dart.symm_involutive

theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ dart.to_prod) d.is_adj.Ne
#align simple_graph.dart.symm_ne SimpleGraph.Dart.symm_ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm :=
  by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp [Sym2.mk'_eq_mk'_iff]
#align simple_graph.dart_edge_eq_iff SimpleGraph.dart_edge_eq_iff

theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {p : V × V}, d.edge = ⟦p⟧ ↔ d.toProd = p ∨ d.toProd = p.swap :=
  by
  rintro ⟨p, h⟩
  apply Sym2.mk'_eq_mk'_iff
#align simple_graph.dart_edge_eq_mk_iff SimpleGraph.dart_edge_eq_mk'_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V}, d.edge = ⟦(u, v)⟧ ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u :=
  by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk_iff]
  simp
#align simple_graph.dart_edge_eq_mk_iff' SimpleGraph.dart_edge_eq_mk'_iff'

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst
#align simple_graph.dart_adj SimpleGraph.DartAdj

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩
#align simple_graph.dart_of_neighbor_set SimpleGraph.dartOfNeighborSet

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'
#align simple_graph.dart_of_neighbor_set_injective SimpleGraph.dartOfNeighborSet_injective

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart :=
  by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩
#align simple_graph.nonempty_dart_top SimpleGraph.nonempty_dart_top

end Darts

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
#align simple_graph.incidence_set SimpleGraph.incidenceSet

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1
#align simple_graph.incidence_set_subset SimpleGraph.incidenceSet_subset

theorem mk'_mem_incidenceSet_iff : ⟦(b, c)⟧ ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff
#align simple_graph.mk_mem_incidence_set_iff SimpleGraph.mk'_mem_incidenceSet_iff

theorem mk'_mem_incidenceSet_left_iff : ⟦(a, b)⟧ ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk'_left _ _
#align simple_graph.mk_mem_incidence_set_left_iff SimpleGraph.mk'_mem_incidenceSet_left_iff

theorem mk'_mem_incidenceSet_right_iff : ⟦(a, b)⟧ ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk'_right _ _
#align simple_graph.mk_mem_incidence_set_right_iff SimpleGraph.mk'_mem_incidenceSet_right_iff

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2
#align simple_graph.edge_mem_incidence_set_iff SimpleGraph.edge_mem_incidenceSet_iff

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {⟦(a, b)⟧} := fun e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩
#align simple_graph.incidence_set_inter_incidence_set_subset SimpleGraph.incidenceSet_inter_incidenceSet_subset

theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {⟦(a, b)⟧} :=
  by
  refine' (G.incidence_set_inter_incidence_set_subset <| h.ne).antisymm _
  rintro _ (rfl : _ = ⟦(a, b)⟧)
  exact ⟨G.mk_mem_incidence_set_left_iff.2 h, G.mk_mem_incidence_set_right_iff.2 h⟩
#align simple_graph.incidence_set_inter_incidence_set_of_adj SimpleGraph.incidenceSet_inter_incidenceSet_of_adj

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk_mem_incidence_set_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidence_set_inter_incidence_set_subset h ⟨ha, hb⟩]
#align simple_graph.adj_of_mem_incidence_set SimpleGraph.adj_of_mem_incidenceSet

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ :=
  by
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidence_set hn ha hb)
#align simple_graph.incidence_set_inter_incidence_set_of_not_adj SimpleGraph.incidenceSet_inter_incidenceSet_of_not_adj

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) := fun e => And.decidable
#align simple_graph.decidable_mem_incidence_set SimpleGraph.decidableMemIncidenceSet

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edge_set` of the graph as a `finset`.
-/
@[reducible]
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
#align simple_graph.edge_finset SimpleGraph.edgeFinset

@[simp, norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _
#align simple_graph.coe_edge_finset SimpleGraph.coe_edgeFinset

variable {G}

@[simp]
theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset
#align simple_graph.mem_edge_finset SimpleGraph.mem_edgeFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1
#align simple_graph.not_is_diag_of_mem_edge_finset SimpleGraph.not_isDiag_of_mem_edgeFinset

@[simp]
theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp [edge_finset]
#align simple_graph.edge_finset_inj SimpleGraph.edgeFinset_inj

@[simp]
theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by
  simp [edge_finset]
#align simple_graph.edge_finset_subset_edge_finset SimpleGraph.edgeFinset_subset_edgeFinset

@[simp]
theorem edgeFinset_sSubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by
  simp [edge_finset]
#align simple_graph.edge_finset_ssubset_edge_finset SimpleGraph.edgeFinset_sSubset_edgeFinset

alias edge_finset_subset_edge_finset ↔ _ edge_finset_mono
#align simple_graph.edge_finset_mono SimpleGraph.edgeFinset_mono

alias edge_finset_ssubset_edge_finset ↔ _ edge_finset_strict_mono
#align simple_graph.edge_finset_strict_mono SimpleGraph.edgeFinset_strict_mono

attribute [mono] edge_finset_mono edge_finset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edge_finset]
#align simple_graph.edge_finset_bot SimpleGraph.edgeFinset_bot

@[simp]
theorem edgeFinset_sup [DecidableEq V] : (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by
  simp [edge_finset]
#align simple_graph.edge_finset_sup SimpleGraph.edgeFinset_sup

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edge_finset]
#align simple_graph.edge_finset_inf SimpleGraph.edgeFinset_inf

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] : (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset :=
  by simp [edge_finset]
#align simple_graph.edge_finset_sdiff SimpleGraph.edgeFinset_sdiff

theorem edgeFinset_card : G.edgeFinset.card = Fintype.card G.edgeSet :=
  Set.toFinset_card _
#align simple_graph.edge_finset_card SimpleGraph.edgeFinset_card

@[simp]
theorem edgeSet_univ_card : (univ : Finset G.edgeSet).card = G.edgeFinset.card :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset
#align simple_graph.edge_set_univ_card SimpleGraph.edgeSet_univ_card

end EdgeFinset

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_neighbor_set SimpleGraph.mem_neighborSet

@[simp]
theorem mem_incidenceSet (v w : V) : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidence_set]
#align simple_graph.mem_incidence_set SimpleGraph.mem_incidenceSet

theorem mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v :=
  by simp only [mem_incidence_set, mem_neighbor_set]
#align simple_graph.mem_incidence_iff_neighbor SimpleGraph.mem_incidence_iff_neighbor

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet h.other = {e} :=
  by
  ext e'
  simp only [incidence_set, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine' ⟨fun h' => _, _⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩
#align simple_graph.adj_incidence_set_inter SimpleGraph.adj_incidenceSet_inter

theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) :=
  by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighbor_set, compl_adj] at h'
  exact h'.2 h
#align simple_graph.compl_neighbor_set_disjoint SimpleGraph.compl_neighborSet_disjoint

theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ :=
  by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighbor_set, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto
#align simple_graph.neighbor_set_union_compl_neighbor_set_eq SimpleGraph.neighborSet_union_compl_neighborSet_eq

-- TODO find out why TC inference has `h` failing a defeq check for `to_finset`
theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [h : Fintype (G.neighborSet v ∪ Gᶜ.neighborSet v : Set V)] :
    (@Set.toFinset _ (G.neighborSet v ∪ Gᶜ.neighborSet v) h).card = Fintype.card V - 1 := by
  classical simp_rw [neighbor_set_union_compl_neighbor_set_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]
#align simple_graph.card_neighbor_set_union_compl_neighbor_set SimpleGraph.card_neighborSet_union_compl_neighborSet

theorem neighborSet_compl (G : SimpleGraph V) (v : V) : Gᶜ.neighborSet v = G.neighborSet vᶜ \ {v} :=
  by
  ext w
  simp [and_comm', eq_comm]
#align simple_graph.neighbor_set_compl SimpleGraph.neighborSet_compl

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w
#align simple_graph.common_neighbors SimpleGraph.commonNeighbors

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl
#align simple_graph.common_neighbors_eq SimpleGraph.commonNeighbors_eq

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl
#align simple_graph.mem_common_neighbors SimpleGraph.mem_commonNeighbors

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _
#align simple_graph.common_neighbors_symm SimpleGraph.commonNeighbors_symm

theorem not_mem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl
#align simple_graph.not_mem_common_neighbors_left SimpleGraph.not_mem_commonNeighbors_left

theorem not_mem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl
#align simple_graph.not_mem_common_neighbors_right SimpleGraph.not_mem_commonNeighbors_right

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left _ _
#align simple_graph.common_neighbors_subset_neighbor_set_left SimpleGraph.commonNeighbors_subset_neighborSet_left

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right _ _
#align simple_graph.common_neighbors_subset_neighbor_set_right SimpleGraph.commonNeighbors_subset_neighborSet_right

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) := fun a => And.decidable
#align simple_graph.decidable_mem_common_neighbors SimpleGraph.decidableMemCommonNeighbors

theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} :=
  by
  ext u
  simp [common_neighbors, eq_comm, not_or_distrib.symm]
#align simple_graph.common_neighbors_top_eq SimpleGraph.commonNeighbors_top_eq

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  h.2.other'
#align simple_graph.other_vertex_of_incident SimpleGraph.otherVertexOfIncident

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) :=
  by
  use h.1
  simp [other_vertex_of_incident, Sym2.other_mem']
#align simple_graph.edge_other_incident_set SimpleGraph.edge_other_incident_set

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v :=
  by
  cases' h with he hv
  rwa [← Sym2.other_spec' hv, mem_edge_set] at he
#align simple_graph.incidence_other_prop SimpleGraph.incidence_other_prop

@[simp]
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)
#align simple_graph.incidence_other_neighbor_edge SimpleGraph.incidence_other_neighbor_edge

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v
    where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [other_vertex_of_incident]
  right_inv := fun ⟨w, hw⟩ => by simp
#align simple_graph.incidence_set_equiv_neighbor_set SimpleGraph.incidenceSetEquivNeighborSet

end Incidence

/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `simple_graph.subgraph.delete_edges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V
    where
  Adj := G.Adj \ Sym2.ToRel s
  symm a b := by simp [adj_comm, Sym2.eq_swap]
#align simple_graph.delete_edges SimpleGraph.deleteEdges

@[simp]
theorem deleteEdges_adj (s : Set (Sym2 V)) (v w : V) :
    (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬⟦(v, w)⟧ ∈ s :=
  Iff.rfl
#align simple_graph.delete_edges_adj SimpleGraph.deleteEdges_adj

theorem sdiff_eq_deleteEdges (G G' : SimpleGraph V) : G \ G' = G.deleteEdges G'.edgeSet :=
  by
  ext
  simp
#align simple_graph.sdiff_eq_delete_edges SimpleGraph.sdiff_eq_deleteEdges

theorem deleteEdges_eq_sdiff_fromEdgeSet (s : Set (Sym2 V)) : G.deleteEdges s = G \ fromEdgeSet s :=
  by
  ext
  exact ⟨fun h => ⟨h.1, not_and_of_not_left _ h.2⟩, fun h => ⟨h.1, not_and'.mp h.2 h.Ne⟩⟩
#align simple_graph.delete_edges_eq_sdiff_from_edge_set SimpleGraph.deleteEdges_eq_sdiff_fromEdgeSet

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : SimpleGraph V).deleteEdges G.edgeSet :=
  by
  ext
  simp
#align simple_graph.compl_eq_delete_edges SimpleGraph.compl_eq_deleteEdges

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') :=
  by
  ext
  simp [and_assoc', not_or]
#align simple_graph.delete_edges_delete_edges SimpleGraph.deleteEdges_deleteEdges

@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G :=
  by
  ext
  simp
#align simple_graph.delete_edges_empty_eq SimpleGraph.deleteEdges_empty_eq

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ :=
  by
  ext
  simp
#align simple_graph.delete_edges_univ_eq SimpleGraph.deleteEdges_univ_eq

theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G :=
  by
  intro
  simp (config := { contextual := true })
#align simple_graph.delete_edges_le SimpleGraph.deleteEdges_le

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w =>
  by
  simp (config := { contextual := true }) only [delete_edges_adj, and_imp, true_and_iff]
  exact fun ha hn hs => hn (h hs)
#align simple_graph.delete_edges_le_of_le SimpleGraph.deleteEdges_le_of_le

theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) :=
  by
  ext
  simp (config := { contextual := true }) [imp_false]
#align simple_graph.delete_edges_eq_inter_edge_set SimpleGraph.deleteEdges_eq_inter_edgeSet

theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H :=
  by
  ext (v w)
  constructor <;> simp (config := { contextual := true }) [@h v w]
#align simple_graph.delete_edges_sdiff_eq_of_le SimpleGraph.deleteEdges_sdiff_eq_of_le

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s :=
  by
  ext e
  refine' Sym2.ind _ e
  simp
#align simple_graph.edge_set_delete_edges SimpleGraph.edgeSet_deleteEdges

theorem edgeFinset_deleteEdges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) [DecidableRel (G.deleteEdges s).Adj] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s :=
  by
  ext e
  simp [edge_set_delete_edges]
#align simple_graph.edge_finset_delete_edges SimpleGraph.edgeFinset_deleteEdges

section DeleteFar

variable (G) [OrderedRing 𝕜] [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ s.card
#align simple_graph.delete_far SimpleGraph.DeleteFar

open Classical

variable {G}

theorem deleteFar_iff :
    G.DeleteFar p r ↔ ∀ ⦃H⦄, H ≤ G → p H → r ≤ G.edgeFinset.card - H.edgeFinset.card :=
  by
  refine' ⟨fun h H hHG hH => _, fun h s hs hG => _⟩
  · have := h (sdiff_subset G.edge_finset H.edge_finset)
    simp only [delete_edges_sdiff_eq_of_le _ hHG, edge_finset_mono hHG, card_sdiff,
      card_le_of_subset, coe_sdiff, coe_edge_finset, Nat.cast_sub] at this
    exact this hH
  ·
    simpa [card_sdiff hs, edge_finset_delete_edges, -Set.toFinset_card, Nat.cast_sub,
      card_le_of_subset hs] using h (G.delete_edges_le s) hG
#align simple_graph.delete_far_iff SimpleGraph.deleteFar_iff

alias delete_far_iff ↔ delete_far.le_card_sub_card _
#align simple_graph.delete_far.le_card_sub_card SimpleGraph.DeleteFar.le_card_sub_card

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun s hs hG =>
  hr.trans <| h hs hG
#align simple_graph.delete_far.mono SimpleGraph.DeleteFar.mono

end DeleteFar

/-! ## Map and comap -/


/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `simple_graph.map_injective`). -/
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W
    where Adj := Relation.Map G.Adj f f
#align simple_graph.map SimpleGraph.map

@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl
#align simple_graph.map_adj SimpleGraph.map_adj

theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) :=
  by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩
#align simple_graph.map_monotone SimpleGraph.map_monotone

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `simple_graph.induce` for a wrapper.

This is surjective when `f` is injective (see `simple_graph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V
    where Adj u v := G.Adj (f u) (f v)
#align simple_graph.comap SimpleGraph.comap

theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) :=
  by
  intro G G' h _ _ ha
  exact h ha
#align simple_graph.comap_monotone SimpleGraph.comap_monotone

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G :=
  by
  ext
  simp
#align simple_graph.comap_map_eq SimpleGraph.comap_map_eq

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f
#align simple_graph.left_inverse_comap_map SimpleGraph.leftInverse_comap_map

theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).Injective
#align simple_graph.map_injective SimpleGraph.map_injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).Surjective
#align simple_graph.comap_surjective SimpleGraph.comap_surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩,
    by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩
#align simple_graph.map_le_iff_le_comap SimpleGraph.map_le_iff_le_comap

theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G :=
  by
  rw [map_le_iff_le_comap]
  exact le_refl _
#align simple_graph.map_comap_le SimpleGraph.map_comap_le

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `simple_graph V` and `simple_graph s`.

There is also a notion of induced subgraphs (see `simple_graph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `simple_graph.comap`. -/
@[reducible]
def induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
#align simple_graph.induce SimpleGraph.induce

/-- Given a graph on a set of vertices, we can make it be a `simple_graph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `simple_graph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)
#align simple_graph.spanning_coe SimpleGraph.spanningCoe

theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _
#align simple_graph.induce_spanning_coe SimpleGraph.induce_spanningCoe

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _
#align simple_graph.spanning_coe_induce_le SimpleGraph.spanningCoe_induce_le

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/


variable (v) [Fintype (G.neighborSet v)]

/-- `G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
#align simple_graph.neighbor_finset SimpleGraph.neighborFinset

theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl
#align simple_graph.neighbor_finset_def SimpleGraph.neighborFinset_def

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset
#align simple_graph.mem_neighbor_finset SimpleGraph.mem_neighborFinset

@[simp]
theorem not_mem_neighborFinset_self : v ∉ G.neighborFinset v :=
  (mem_neighborFinset _ _ _).Not.mpr <| G.loopless _
#align simple_graph.not_mem_neighbor_finset_self SimpleGraph.not_mem_neighborFinset_self

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| not_mem_neighborFinset_self _ _
#align simple_graph.neighbor_finset_disjoint_singleton SimpleGraph.neighborFinset_disjoint_singleton

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| not_mem_neighborFinset_self _ _
#align simple_graph.singleton_disjoint_neighbor_finset SimpleGraph.singleton_disjoint_neighborFinset

/-- `G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ :=
  (G.neighborFinset v).card
#align simple_graph.degree SimpleGraph.degree

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm
#align simple_graph.card_neighbor_set_eq_degree SimpleGraph.card_neighborSet_eq_degree

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighbor_finset]
#align simple_graph.degree_pos_iff_exists_adj SimpleGraph.degree_pos_iff_exists_adj

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighbor_set_union_compl_neighbor_set G v, Set.toFinset_union]
    simp [card_disjoint_union (set.disjoint_to_finset.mpr (compl_neighbor_set_disjoint G v))]
#align simple_graph.degree_compl SimpleGraph.degree_compl

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm
#align simple_graph.incidence_set_fintype SimpleGraph.incidenceSetFintype

/-- This is the `finset` version of `incidence_set`.
-/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset
#align simple_graph.incidence_finset SimpleGraph.incidenceFinset

@[simp]
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v :=
  by
  rw [Fintype.card_congr (G.incidence_set_equiv_neighbor_set v)]
  simp
#align simple_graph.card_incidence_set_eq_degree SimpleGraph.card_incidenceSet_eq_degree

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] : (G.incidenceFinset v).card = G.degree v :=
  by
  rw [← G.card_incidence_set_eq_degree]
  apply Set.toFinset_card
#align simple_graph.card_incidence_finset_eq_degree SimpleGraph.card_incidenceFinset_eq_degree

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset
#align simple_graph.mem_incidence_finset SimpleGraph.mem_incidenceFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = G.edgeFinset.filter (Membership.Mem v) :=
  by
  ext e
  refine' Sym2.ind (fun x y => _) e
  simp [mk_mem_incidence_set_iff]
#align simple_graph.incidence_finset_eq_filter SimpleGraph.incidenceFinset_eq_filter

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)
#align simple_graph.locally_finite SimpleGraph.LocallyFinite

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d
#align simple_graph.is_regular_of_degree SimpleGraph.IsRegularOfDegree

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v
#align simple_graph.is_regular_of_degree.degree_eq SimpleGraph.IsRegularOfDegree.degree_eq

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) :=
  by
  intro v
  rw [degree_compl, h v]
#align simple_graph.is_regular_of_degree.compl SimpleGraph.IsRegularOfDegree.compl

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ _
    (by
      simp_rw [mem_neighbor_set]
      infer_instance)
    _
#align simple_graph.neighbor_set_fintype SimpleGraph.neighborSetFintype

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = Finset.univ.filter (G.Adj v) :=
  by
  ext
  simp
#align simple_graph.neighbor_finset_eq_filter SimpleGraph.neighborFinset_eq_filter

theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = G.neighborFinset vᶜ \ {v} := by
  simp only [neighbor_finset, neighbor_set_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]
#align simple_graph.neighbor_finset_compl SimpleGraph.neighborFinset_compl

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]
#align simple_graph.complete_graph_degree SimpleGraph.complete_graph_degree

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 :=
  by
  erw [degree, neighbor_finset_eq_filter, filter_false]
  exact Finset.card_empty
#align simple_graph.bot_degree SimpleGraph.bot_degree

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) :=
  by
  intro v
  simp
#align simple_graph.is_regular_of_degree.top SimpleGraph.IsRegularOfDegree.top

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untop' 0 (univ.image fun v => G.degree v).min
#align simple_graph.min_degree SimpleGraph.minDegree

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v :=
  by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  refine' ⟨v, by simp [min_degree, ht]⟩
#align simple_graph.exists_minimal_degree_vertex SimpleGraph.exists_minimal_degree_vertex

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v :=
  by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [min_degree, ht]
#align simple_graph.min_degree_le_degree SimpleGraph.minDegree_le_degree

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree :=
  by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h
#align simple_graph.le_min_degree_of_forall_le_degree SimpleGraph.le_minDegree_of_forall_le_degree

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  Option.getD (univ.image fun v => G.degree v).max 0
#align simple_graph.max_degree SimpleGraph.maxDegree

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v :=
  by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, rfl⟩
  refine' ⟨v, _⟩
  rw [max_degree, ht]
  rfl
#align simple_graph.exists_maximal_degree_vertex SimpleGraph.exists_maximal_degree_vertex

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree :=
  by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [max_degree, ht]
#align simple_graph.degree_le_max_degree SimpleGraph.degree_le_maxDegree

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [max_degree, hV, image_empty]
    exact zero_le k
#align simple_graph.max_degree_le_of_forall_degree_le SimpleGraph.maxDegree_le_of_forall_degree_le

theorem degree_lt_card_verts [DecidableRel G.Adj] (v : V) : G.degree v < Fintype.card V := by
  classical
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    exact ⟨v, by simp, Finset.subset_univ _⟩
#align simple_graph.degree_lt_card_verts SimpleGraph.degree_lt_card_verts

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] : G.maxDegree < Fintype.card V :=
  by
  cases' G.exists_maximal_degree_vertex with v hv
  rw [hv]
  apply G.degree_lt_card_verts v
#align simple_graph.max_degree_lt_card_verts SimpleGraph.maxDegree_lt_card_verts

theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v :=
  by
  rw [← card_neighbor_set_eq_degree]
  exact Set.card_le_of_subset (Set.inter_subset_left _ _)
#align simple_graph.card_common_neighbors_le_degree_left SimpleGraph.card_commonNeighbors_le_degree_left

theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [common_neighbors_symm _ v w, card_common_neighbors_le_degree_left]
#align simple_graph.card_common_neighbors_le_degree_right SimpleGraph.card_commonNeighbors_le_degree_right

theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)
#align simple_graph.card_common_neighbors_lt_card_verts SimpleGraph.card_commonNeighbors_lt_card_verts

/-- If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
    erw [← Set.toFinset_card]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    use w
    constructor
    · rw [Set.mem_toFinset]
      apply not_mem_common_neighbors_right
    · rw [Finset.insert_subset]
      constructor
      · simpa
      · rw [neighbor_finset, Set.toFinset_subset_toFinset]
        exact G.common_neighbors_subset_neighbor_set_left _ _
#align simple_graph.adj.card_common_neighbors_lt_degree SimpleGraph.Adj.card_commonNeighbors_lt_degree

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 :=
  by
  simp only [common_neighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]
#align simple_graph.card_common_neighbors_top SimpleGraph.card_commonNeighbors_top

end Finite

section Maps

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbrev Hom :=
  RelHom G.Adj G'.Adj
#align simple_graph.hom SimpleGraph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.adj f(v) f(w) ↔ G.adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
#align simple_graph.embedding SimpleGraph.Embedding

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj
#align simple_graph.iso SimpleGraph.Iso

-- mathport name: «expr →g »
infixl:50 " →g " => Hom

-- mathport name: «expr ↪g »
infixl:50 " ↪g " => Embedding

-- mathport name: «expr ≃g »
infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbrev id : G →g G :=
  RelHom.id _
#align simple_graph.hom.id SimpleGraph.Hom.id

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
#align simple_graph.hom.map_adj SimpleGraph.Hom.map_adj

theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Quotient.ind (fun e h => Sym2.fromRel_prop.mpr (f.map_rel' h)) e h
#align simple_graph.hom.map_mem_edge_set SimpleGraph.Hom.map_mem_edgeSet

theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h
#align simple_graph.hom.apply_mem_neighbor_set SimpleGraph.Hom.apply_mem_neighborSet

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edge_set e.property⟩
#align simple_graph.hom.map_edge_set SimpleGraph.Hom.mapEdgeSet

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighbor_set w.property⟩
#align simple_graph.hom.map_neighbor_set SimpleGraph.Hom.mapNeighborSet

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩
#align simple_graph.hom.map_dart SimpleGraph.Hom.mapDart

@[simp]
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl
#align simple_graph.hom.map_dart_apply SimpleGraph.Hom.mapDart_apply

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G'
    where
  toFun x := x
  map_rel' := h
#align simple_graph.hom.map_spanning_subgraphs SimpleGraph.Hom.mapSpanningSubgraphs

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet :=
  by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [hom.map_edge_set]
  repeat' rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj
#align simple_graph.hom.map_edge_set.injective SimpleGraph.Hom.mapEdgeSet.injective

/-- Every graph homomomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f :=
  by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))
#align simple_graph.hom.injective_of_top_hom SimpleGraph.Hom.injective_of_top_hom

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `simple_graph.embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G
    where
  toFun := f
  map_rel' := by simp
#align simple_graph.hom.comap SimpleGraph.Hom.comap

variable {G'' : SimpleGraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  f'.comp f
#align simple_graph.hom.comp SimpleGraph.Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.hom.coe_comp SimpleGraph.Hom.coe_comp

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _
#align simple_graph.embedding.refl SimpleGraph.Embedding.refl

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom
#align simple_graph.embedding.to_hom SimpleGraph.Embedding.toHom

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.embedding.map_adj_iff SimpleGraph.Embedding.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Quotient.ind (fun ⟨v, w⟩ => f.map_adj_iff) e
#align simple_graph.embedding.map_mem_edge_set_iff SimpleGraph.Embedding.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.embedding.apply_mem_neighbor_set_iff SimpleGraph.Embedding.apply_mem_neighborSet_iff

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet
    where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.inj'
#align simple_graph.embedding.map_edge_set SimpleGraph.Embedding.mapEdgeSet

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h⊢
    exact f.inj' h
#align simple_graph.embedding.map_neighbor_set SimpleGraph.Embedding.mapNeighborSet

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
@[simps]
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.comap SimpleGraph.Embedding.comap

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps]
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.map SimpleGraph.Embedding.map

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G
#align simple_graph.embedding.induce SimpleGraph.Embedding.induce

/-- Graphs on a set of vertices embed in their `spanning_coe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G
#align simple_graph.embedding.spanning_coe SimpleGraph.Embedding.spanningCoe

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ↪ β) :
    (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.complete_graph SimpleGraph.Embedding.completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'
#align simple_graph.embedding.comp SimpleGraph.Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.embedding.coe_comp SimpleGraph.Embedding.coe_comp

end Embedding

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _
#align simple_graph.iso.refl SimpleGraph.Iso.refl

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding
#align simple_graph.iso.to_embedding SimpleGraph.Iso.toEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom
#align simple_graph.iso.to_hom SimpleGraph.Iso.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  f.symm
#align simple_graph.iso.symm SimpleGraph.Iso.symm

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.iso.map_adj_iff SimpleGraph.Iso.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Quotient.ind (fun ⟨v, w⟩ => f.map_adj_iff) e
#align simple_graph.iso.map_mem_edge_set_iff SimpleGraph.Iso.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.iso.apply_mem_neighbor_set_iff SimpleGraph.Iso.apply_mem_neighborSet_iff

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet
    where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [hom.map_edge_set, Sym2.map_map, RelIso.coe_coeFn, RelEmbedding.coe_coeFn,
      Subtype.mk_eq_mk, Subtype.coe_mk, coe_coe]
    apply congr_fun
    convert Sym2.map_id
    exact funext fun _ => RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [hom.map_edge_set, Sym2.map_map, RelIso.coe_coeFn, RelEmbedding.coe_coeFn,
      Subtype.mk_eq_mk, Subtype.coe_mk, coe_coe]
    apply congr_fun
    convert Sym2.map_id
    exact funext fun _ => RelIso.apply_symm_apply _ _
#align simple_graph.iso.map_edge_set SimpleGraph.Iso.mapEdgeSet

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      convert f.symm.apply_mem_neighbor_set_iff.mpr w.2
      simp only [RelIso.symm_apply_apply]⟩
  left_inv w := by simp
  right_inv w := by simp
#align simple_graph.iso.map_neighbor_set SimpleGraph.Iso.mapNeighborSet

theorem card_eq_of_iso [Fintype V] [Fintype W] (f : G ≃g G') : Fintype.card V = Fintype.card W := by
  convert (Fintype.ofEquiv_card f.to_equiv).symm
#align simple_graph.iso.card_eq_of_iso SimpleGraph.Iso.card_eq_of_iso

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
@[simps]
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.comap SimpleGraph.Iso.comap

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps]
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.map SimpleGraph.Iso.map

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.complete_graph SimpleGraph.Iso.completeGraph

theorem toEmbedding_completeGraph {α β : Type _} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl
#align simple_graph.iso.to_embedding_complete_graph SimpleGraph.Iso.toEmbedding_completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'
#align simple_graph.iso.comp SimpleGraph.Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.iso.coe_comp SimpleGraph.Iso.coe_comp

end Iso

end Maps

end SimpleGraph

