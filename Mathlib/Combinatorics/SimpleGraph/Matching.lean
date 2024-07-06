/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller, Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity

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
  denoted `M.is_matching`.

* `SimpleGraph.Subgraph.IsPerfectMatching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.IsPerfectMatching`.

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem

* Hall's Marriage Theorem (see combinatorics.hall)
-/

open Function

namespace SimpleGraph
variable {V : Type*} {G G': SimpleGraph V} {M M' : Subgraph G} {v w : V}

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

lemma IsMatching.map_hom_ofLE_IsMatching (h : M.IsMatching) (hGG' : G ≤ G') :
    (M.map (Hom.ofLE hGG')).IsMatching := by
  intro _ hv
  obtain ⟨_, hv, hv'⟩ := Set.mem_image _ _ _ |>.mp hv
  obtain ⟨w, hw⟩ := h hv
  use w
  simpa using hv' ▸ hw

lemma sup_IsMatching (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hd : Disjoint M.support M'.support) : (M ⊔ M').IsMatching := by
  intro v hv
  have aux {N N' : Subgraph G} (hN : N.IsMatching) (hd : Disjoint N.support N'.support)
    (hmN: v ∈ N.verts) : ∃! w, (N ⊔ N').Adj v w := by
    obtain ⟨w, hw⟩ := hN hmN
    use w
    refine ⟨sup_adj.mpr (.inl hw.1), ?_⟩
    intro y hy
    cases hy with
    | inl h => exact hw.2 y h
    | inr h =>
      rw [Set.disjoint_left] at hd
      simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, h⟩] using @hd v
  cases Set.mem_or_mem_of_mem_union hv with
  | inl hmM => exact aux hM hd hmM
  | inr hmM' =>
    rw [sup_comm]
    exact aux hM' (Disjoint.symm hd) hmM'

lemma iSup_IsMatching {ι : Sort _} {f : ι → Subgraph G} (hM : (i : ι) → (f i).IsMatching)
    (hd : (i j : ι) → (i ≠ j) →  Disjoint ((f i).support) ((f j).support)) :
    (⨆ i , f i).IsMatching := by
  intro v hv
  obtain ⟨i , hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w , hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i' , hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd _ _ heq
    rw [Set.disjoint_left] at this
    simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, hi'⟩] using @this v

lemma subgraphOfAdj_IsMatching (h : G.Adj v w) : (G.subgraphOfAdj h).IsMatching := by
  intro _ hv
  rw [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

lemma coe_IsMatching {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching) :
    M.coeSubgraph.IsMatching := by
  intro _ hv
  obtain ⟨w, hw⟩ := hM <| Set.mem_of_mem_image_val <| M.coeSubgraph_verts.symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp <| (coeSubgraph_verts M).symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists_const]
    exact ⟨hv.2 ▸ v.2, hw.1⟩
  · obtain ⟨_, hw', hvw⟩ := (coeSubgraph_adj _ _ _).mp hy
    rw [← hw.2 ⟨y, hw'⟩ hvw]

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
  intro _ hv
  obtain ⟨hv, rfl⟩ := hv
  obtain ⟨w, hvw, hw⟩ := h hv
  use w
  simpa [hv, hvw, M.edge_vert hvw.symm, (M.adj_sub hvw).symm.reachable] using fun _ _ _ ↦ hw _

lemma IsPerfectMatching.induce_connectedComponent_isMatching (h : M.IsPerfectMatching)
    (c : ConnectedComponent G) : (M.induce c.supp).IsMatching := by
  simpa [h.2.verts_eq_univ] using h.1.induce_connectedComponent c

end Subgraph

namespace ConnectedComponent

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn fun w ↦ decidable_of_iff (G.Reachable v w) <| by simp fun _ _ _ _ ↦ Subsingleton.elim _ _

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
      obtain ⟨⟨v', hv'⟩, hv , rfl⟩ := hv
      use w
      have hwnu : w ∉ u := fun hw' ↦ h w hw' ⟨v', hv'⟩ hw.1 hv
      refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy ↦ hw.2 _ hy.2.2⟩
      apply mem_coe_supp_of_adj ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ ⟨by trivial, hwnu⟩
      simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_diff, Set.mem_univ, true_and,
        Subgraph.induce_adj, Subgraph.top_adj, M.adj_sub hw.1] at hv' ⊢
      trivial
    apply Nat.odd_iff_not_even.mp codd
    haveI : Fintype (Subgraph.induce M (Subtype.val '' c.supp)).verts := Fintype.ofFinite _
    haveI : Fintype c.supp := Fintype.ofFinite _
    have hMeven := Subgraph.IsMatching.even_card hMmatch
    simp only [Subgraph.induce_verts, Set.toFinset_image, Nat.card_eq_fintype_card,
      Set.toFinset_card, Finset.card_image_of_injective _ (Subtype.val_injective)] at hMeven ⊢
    exact hMeven

end Finite
end ConnectedComponent
end SimpleGraph
