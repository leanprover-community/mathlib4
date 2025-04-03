/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller, Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

#align_import combinatorics.simple_graph.matching from "leanprover-community/mathlib"@"138448ae98f529ef34eeb61114191975ee2ca508"

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `SimpleGraph.Subgraph.IsMatching`: `M.IsMatching` means that `M` is a matching of its
  underlying graph.

* `SimpleGraph.Subgraph.IsPerfectMatching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.IsPerfectMatching`.

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem

* Hall's Marriage Theorem (see `Mathlib.Combinatorics.Hall.Basic`)
-/

open Function

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {M : Subgraph G} {v w : V}

namespace Subgraph

/--
The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def IsMatching (M : Subgraph G) : Prop := ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.Adj v w
#align simple_graph.subgraph.is_matching SimpleGraph.Subgraph.IsMatching

/-- Given a vertex, returns the unique edge of the matching it is incident to. -/
noncomputable def IsMatching.toEdge (h : M.IsMatching) (v : M.verts) : M.edgeSet :=
  ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩
#align simple_graph.subgraph.is_matching.to_edge SimpleGraph.Subgraph.IsMatching.toEdge

theorem IsMatching.toEdge_eq_of_adj (h : M.IsMatching) (hv : v ∈ M.verts) (hvw : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = ⟨s(v, w), hvw⟩ := by
  simp only [IsMatching.toEdge, Subtype.mk_eq_mk]
  congr
  exact ((h (M.edge_vert hvw)).choose_spec.2 w hvw).symm
#align simple_graph.subgraph.is_matching.to_edge_eq_of_adj SimpleGraph.Subgraph.IsMatching.toEdge_eq_of_adj

theorem IsMatching.toEdge.surjective (h : M.IsMatching) : Surjective h.toEdge := by
  rintro ⟨e, he⟩
  induction' e with x y
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj _ he⟩
#align simple_graph.subgraph.is_matching.to_edge.surjective SimpleGraph.Subgraph.IsMatching.toEdge.surjective

theorem IsMatching.toEdge_eq_toEdge_of_adj (h : M.IsMatching)
    (hv : v ∈ M.verts) (hw : w ∈ M.verts) (ha : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = h.toEdge ⟨w, hw⟩ := by
  rw [h.toEdge_eq_of_adj hv ha, h.toEdge_eq_of_adj hw (M.symm ha), Subtype.mk_eq_mk, Sym2.eq_swap]
#align simple_graph.subgraph.is_matching.to_edge_eq_to_edge_of_adj SimpleGraph.Subgraph.IsMatching.toEdge_eq_toEdge_of_adj

/--
The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def IsPerfectMatching (M : G.Subgraph) : Prop := M.IsMatching ∧ M.IsSpanning
#align simple_graph.subgraph.is_perfect_matching SimpleGraph.Subgraph.IsPerfectMatching

theorem IsMatching.support_eq_verts (h : M.IsMatching) : M.support = M.verts := by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩
#align simple_graph.subgraph.is_matching.support_eq_verts SimpleGraph.Subgraph.IsMatching.support_eq_verts

theorem isMatching_iff_forall_degree [∀ v, Fintype (M.neighborSet v)] :
    M.IsMatching ↔ ∀ v : V, v ∈ M.verts → M.degree v = 1 := by
  simp only [degree_eq_one_iff_unique_adj, IsMatching]
#align simple_graph.subgraph.is_matching_iff_forall_degree SimpleGraph.Subgraph.isMatching_iff_forall_degree

theorem IsMatching.even_card [Fintype M.verts] (h : M.IsMatching) : Even M.verts.toFinset.card := by
  classical
  rw [isMatching_iff_forall_degree] at h
  use M.coe.edgeFinset.card
  rw [← two_mul, ← M.coe.sum_degrees_eq_twice_card_edges]
  -- Porting note: `SimpleGraph.Subgraph.coe_degree` does not trigger because it uses
  -- instance arguments instead of implicit arguments for the first `Fintype` argument.
  -- Using a `convert_to` to swap out the `Fintype` instance to the "right" one.
  convert_to _ = Finset.sum Finset.univ fun v => SimpleGraph.degree (Subgraph.coe M) v using 3
  simp [h, Finset.card_univ]
#align simple_graph.subgraph.is_matching.even_card SimpleGraph.Subgraph.IsMatching.even_card

theorem isPerfectMatching_iff : M.IsPerfectMatching ↔ ∀ v, ∃! w, M.Adj v w := by
  refine ⟨?_, fun hm => ⟨fun v _ => hm v, fun v => ?_⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw
#align simple_graph.subgraph.is_perfect_matching_iff SimpleGraph.Subgraph.isPerfectMatching_iff

theorem isPerfectMatching_iff_forall_degree [∀ v, Fintype (M.neighborSet v)] :
    M.IsPerfectMatching ↔ ∀ v, M.degree v = 1 := by
  simp [degree_eq_one_iff_unique_adj, isPerfectMatching_iff]
#align simple_graph.subgraph.is_perfect_matching_iff_forall_degree SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree

theorem IsPerfectMatching.even_card [Fintype V] (h : M.IsPerfectMatching) :
    Even (Fintype.card V) := by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1
#align simple_graph.subgraph.is_perfect_matching.even_card SimpleGraph.Subgraph.IsPerfectMatching.even_card

lemma IsMatching.induce_connectedComponent (h : M.IsMatching) (c : ConnectedComponent G) :
    (M.induce (M.verts ∩ c.supp)).IsMatching := by
  intro v hv
  simp only [induce_verts, Set.mem_inter_iff, ConnectedComponent.mem_supp_iff] at hv
  obtain ⟨hv, rfl⟩ := hv
  obtain ⟨w, hvw, hw⟩ := h hv
  use w
  simp only [induce_adj, Set.mem_inter_iff, hv, ConnectedComponent.mem_supp_iff, and_self, and_imp,
    true_and, ConnectedComponent.eq, hw, hvw, M.edge_vert hvw.symm, (M.adj_sub hvw).symm.reachable]
  exact fun _ _ _ ↦ hw _

lemma IsPerfectMatching.induce_connectedComponent_isMatching (h : M.IsPerfectMatching)
    (c : ConnectedComponent G) : (M.induce c.supp).IsMatching := by
  simpa [h.2.verts_eq_univ] using h.1.induce_connectedComponent c

end Subgraph

namespace ConnectedComponent

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma even_card_of_isPerfectMatching (c : ConnectedComponent G) (hM : M.IsPerfectMatching) :
    Even (Fintype.card c.supp) := by
  classical simpa using (hM.induce_connectedComponent_isMatching c).even_card

lemma odd_matches_node_outside {u : Set V} {c : ConnectedComponent (Subgraph.deleteVerts ⊤ u).coe}
    (hM : M.IsPerfectMatching) (codd : Odd (Nat.card c.supp)) :
    ∃ᵉ (w ∈ u) (v : ((⊤ : G.Subgraph).deleteVerts u).verts), M.Adj v w ∧ v ∈ c.supp := by
  by_contra! h
  have hMmatch : (M.induce c.supp).IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    obtain ⟨⟨v', hv'⟩, ⟨hv , rfl⟩⟩ := hv
    use w
    have hwnu : w ∉ u := fun hw' ↦ h w hw' ⟨v', hv'⟩ (hw.1) hv
    refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy ↦ hw.2 _ hy.2.2⟩
    apply ConnectedComponent.mem_coe_supp_of_adj ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ ⟨by trivial, hwnu⟩
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ, true_and,
      Subgraph.induce_adj, hwnu, not_false_eq_true, and_self, Subgraph.top_adj, M.adj_sub hw.1,
      and_true] at hv' ⊢
    trivial

  apply Nat.odd_iff_not_even.mp codd
  haveI : Fintype ↑(Subgraph.induce M (Subtype.val '' supp c)).verts := Fintype.ofFinite _
  have hMeven := Subgraph.IsMatching.even_card hMmatch
  haveI : Fintype (c.supp) := Fintype.ofFinite _
  simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.toFinset_image,
    Nat.card_eq_fintype_card, Set.toFinset_image,
    Finset.card_image_of_injective _ (Subtype.val_injective), Set.toFinset_card] at hMeven ⊢
  exact hMeven

end Finite
end ConnectedComponent
end SimpleGraph
