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


universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} (M : Subgraph G)

namespace Subgraph

/--
The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def IsMatching : Prop := ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.Adj v w
#align simple_graph.subgraph.is_matching SimpleGraph.Subgraph.IsMatching

/-- Given a vertex, returns the unique edge of the matching it is incident to. -/
noncomputable def IsMatching.toEdge {M : Subgraph G} (h : M.IsMatching) (v : M.verts) : M.edgeSet :=
  ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩
#align simple_graph.subgraph.is_matching.to_edge SimpleGraph.Subgraph.IsMatching.toEdge

theorem IsMatching.toEdge_eq_of_adj {M : Subgraph G} (h : M.IsMatching) {v w : V} (hv : v ∈ M.verts)
    (hvw : M.Adj v w) : h.toEdge ⟨v, hv⟩ = ⟨s(v, w), hvw⟩ := by
  simp only [IsMatching.toEdge, Subtype.mk_eq_mk]
  congr
  exact ((h (M.edge_vert hvw)).choose_spec.2 w hvw).symm
#align simple_graph.subgraph.is_matching.to_edge_eq_of_adj SimpleGraph.Subgraph.IsMatching.toEdge_eq_of_adj

theorem IsMatching.toEdge.surjective {M : Subgraph G} (h : M.IsMatching) :
    Function.Surjective h.toEdge := by
  rintro ⟨e, he⟩
  refine Sym2.ind (fun x y he => ?_) e he
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj _ he⟩
#align simple_graph.subgraph.is_matching.to_edge.surjective SimpleGraph.Subgraph.IsMatching.toEdge.surjective

theorem IsMatching.toEdge_eq_toEdge_of_adj {M : Subgraph G} {v w : V} (h : M.IsMatching)
    (hv : v ∈ M.verts) (hw : w ∈ M.verts) (ha : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = h.toEdge ⟨w, hw⟩ := by
  rw [h.toEdge_eq_of_adj hv ha, h.toEdge_eq_of_adj hw (M.symm ha), Subtype.mk_eq_mk, Sym2.eq_swap]
#align simple_graph.subgraph.is_matching.to_edge_eq_to_edge_of_adj SimpleGraph.Subgraph.IsMatching.toEdge_eq_toEdge_of_adj

/--
The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def IsPerfectMatching : Prop := M.IsMatching ∧ M.IsSpanning
#align simple_graph.subgraph.is_perfect_matching SimpleGraph.Subgraph.IsPerfectMatching

theorem IsMatching.support_eq_verts {M : Subgraph G} (h : M.IsMatching) : M.support = M.verts := by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩
#align simple_graph.subgraph.is_matching.support_eq_verts SimpleGraph.Subgraph.IsMatching.support_eq_verts

theorem isMatching_iff_forall_degree {M : Subgraph G} [∀ v : V, Fintype (M.neighborSet v)] :
    M.IsMatching ↔ ∀ v : V, v ∈ M.verts → M.degree v = 1 := by
  simp only [degree_eq_one_iff_unique_adj, IsMatching]
#align simple_graph.subgraph.is_matching_iff_forall_degree SimpleGraph.Subgraph.isMatching_iff_forall_degree

theorem IsMatching.even_card {M : Subgraph G} [Fintype M.verts] (h : M.IsMatching) :
    Even M.verts.toFinset.card := by
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
  refine' ⟨_, fun hm => ⟨fun v _ => hm v, fun v => _⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw
#align simple_graph.subgraph.is_perfect_matching_iff SimpleGraph.Subgraph.isPerfectMatching_iff

theorem isPerfectMatching_iff_forall_degree {M : Subgraph G} [∀ v, Fintype (M.neighborSet v)] :
    M.IsPerfectMatching ↔ ∀ v, M.degree v = 1 := by
  simp [degree_eq_one_iff_unique_adj, isPerfectMatching_iff]
#align simple_graph.subgraph.is_perfect_matching_iff_forall_degree SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree

theorem IsPerfectMatching.even_card {M : Subgraph G} [Fintype V] (h : M.IsPerfectMatching) :
    Even (Fintype.card V) := by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1
#align simple_graph.subgraph.is_perfect_matching.even_card SimpleGraph.Subgraph.IsPerfectMatching.even_card

lemma isPerfectMatching_induce_supp_isMatching {M : Subgraph G} (h : Subgraph.IsPerfectMatching M)
    (c : ConnectedComponent G) : (M.induce c.supp).IsMatching  := by
    intro v hv
    obtain ⟨ w, hw ⟩ := h.1 (h.2 _)
    use w
    constructor
    · constructor
      · assumption
      · constructor
        · rw [ConnectedComponent.mem_supp_iff] at *
          rw [← hv]
          apply ConnectedComponent.connectedComponentMk_eq_of_adj
          apply M.adj_sub
          rw [Subgraph.adj_comm]
          exact hw.1
        · exact hw.1
    · intro y hy
      exact hw.2 y hy.2.2

end Subgraph

namespace ConnectedComponent

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/--
 Decidable instance for membership of support of a connected component.
-/
instance (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn
    (fun w => by simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]; infer_instance)
    (fun _ _ _ _ => Subsingleton.elim _ _)

lemma even_if_perfect_matching {M : Subgraph G} (c : ConnectedComponent G)
    (hM : Subgraph.IsPerfectMatching M) : Even (Fintype.card ↑(ConnectedComponent.supp c)) := by
    classical
    obtain ⟨ k , hk ⟩ := (M.isPerfectMatching_induce_supp_isMatching hM c).even_card
    use k
    rw [← hk, Subgraph.induce_verts, Fintype.card_ofFinset]
    congr
    simp only [ConnectedComponent.mem_supp_iff, Finset.mem_univ, forall_true_left]
    exact Set.filter_mem_univ_eq_toFinset fun x => connectedComponentMk G x = c

/--
  Local instance of Fintype for sets in a Fintype.
  Chosen as local because it is noncomputable.
-/
noncomputable local instance (u : Set V) : Fintype u := Fintype.ofFinite ↑u


theorem mem_supp_of_adj {u : Set V} {v w : V}
    {c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe}
    (hv : v ∈ Subtype.val '' c.supp) (hw : w ∈ ((⊤ : Subgraph G).deleteVerts  u).verts)
    (hadj : G.Adj v w) : w ∈ Subtype.val '' c.supp := by
    rw [Set.mem_image]
    obtain ⟨ v' , hv' ⟩ := hv
    use ⟨ w , ⟨ by trivial , by refine Set.not_mem_of_mem_diff hw ⟩ ⟩
    rw [ConnectedComponent.mem_supp_iff]
    constructor
    · rw [← (ConnectedComponent.mem_supp_iff _ _).mp hv'.1]
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      apply SimpleGraph.Subgraph.Adj.coe
      rw [Subgraph.deleteVerts_adj]
      constructor
      · trivial
      · constructor
        · exact Set.not_mem_of_mem_diff hw
        · constructor
          · trivial
          · constructor
            · exact v'.prop.2
            · rw [Subgraph.top_adj]
              rw [hv'.2]
              exact adj_symm G hadj
    · rfl

lemma odd_matches_node_outside {M : Subgraph G} {u : Set V}
    {c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe}
    (hM : Subgraph.IsPerfectMatching M)
    (codd : c.isOdd) : ∃ (w : u.Elem) (v : ((⊤ : G.Subgraph).deleteVerts u).verts.Elem),
        M.Adj v w ∧ v ∈ c.supp := by
    rw [ConnectedComponent.isOdd_iff] at codd
    by_contra! h
    have h' : (M.induce c.supp).IsMatching := by
      intro v hv
      obtain ⟨ w , hw ⟩ := hM.1 (hM.2 v)
      obtain ⟨ v' , hv' ⟩ := hv
      use w
      constructor
      · constructor
        · exact ⟨ v' , hv' ⟩
        · constructor
          · have h'' : w ∉ u := by
              intro hw'
              apply h ⟨ w , hw' ⟩ v' _
              · exact hv'.1
              rw [hv'.2]
              exact hw.1
            apply mem_supp_of_adj ⟨ v' , ⟨ hv'.1 , rfl ⟩ ⟩ ⟨ by trivial , h'' ⟩
            rw [hv'.2]
            exact Subgraph.adj_sub _ hw.1
          · exact hw.1
      · intro y hy
        apply hw.2
        exact hy.2.2

    apply Nat.odd_iff_not_even.mp codd
    have h'' := Subgraph.IsMatching.even_card h'
    simp only [Subgraph.induce_verts, Subgraph.verts_top] at h''

    rw [Nat.even_iff] at h'' ⊢
    rw [← h'', Set.toFinset_image, Finset.card_image_of_injective _ (Subtype.val_injective)]
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.toFinset_card]


end Finite

end ConnectedComponent


end SimpleGraph
