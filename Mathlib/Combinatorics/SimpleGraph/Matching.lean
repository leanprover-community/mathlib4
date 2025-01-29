/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller, Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Functor

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

* `SimpleGraph.IsMatchingFree` means that a graph `G` has no perfect matchings.

* `SimpleGraph.IsCycles` means that a graph consists of cycles (including cycles of length 0,
  also known as isolated vertices)

* `SimpleGraph.IsAlternating` means that edges in a graph `G` are alternatingly
  included and not included in some other graph `G'`

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem

* Hall's Marriage Theorem (see `Mathlib.Combinatorics.Hall.Basic`)
-/

assert_not_exists TwoSidedIdeal

open Function

namespace SimpleGraph
variable {V W : Type*} {G G': SimpleGraph V} {M M' : Subgraph G} {v w : V}

namespace Subgraph

/--
The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def IsMatching (M : Subgraph G) : Prop := ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.Adj v w

/-- Given a vertex, returns the unique edge of the matching it is incident to. -/
noncomputable def IsMatching.toEdge (h : M.IsMatching) (v : M.verts) : M.edgeSet :=
  ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩

theorem IsMatching.toEdge_eq_of_adj (h : M.IsMatching) (hv : v ∈ M.verts) (hvw : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = ⟨s(v, w), hvw⟩ := by
  simp only [IsMatching.toEdge, Subtype.mk_eq_mk]
  congr
  exact ((h (M.edge_vert hvw)).choose_spec.2 w hvw).symm

theorem IsMatching.toEdge.surjective (h : M.IsMatching) : Surjective h.toEdge := by
  rintro ⟨e, he⟩
  induction' e with x y
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj _ he⟩

theorem IsMatching.toEdge_eq_toEdge_of_adj (h : M.IsMatching)
    (hv : v ∈ M.verts) (hw : w ∈ M.verts) (ha : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = h.toEdge ⟨w, hw⟩ := by
  rw [h.toEdge_eq_of_adj hv ha, h.toEdge_eq_of_adj hw (M.symm ha), Subtype.mk_eq_mk, Sym2.eq_swap]

lemma IsMatching.map_ofLE (h : M.IsMatching) (hGG' : G ≤ G') :
    (M.map (Hom.ofLE hGG')).IsMatching := by
  intro _ hv
  obtain ⟨_, hv, hv'⟩ := Set.mem_image _ _ _ |>.mp hv
  obtain ⟨w, hw⟩ := h hv
  use w
  simpa using hv' ▸ hw

lemma IsMatching.sup (hM : M.IsMatching) (hM' : M'.IsMatching)
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

lemma IsMatching.iSup {ι : Sort _} {f : ι → Subgraph G} (hM : (i : ι) → (f i).IsMatching)
    (hd : Pairwise fun i j ↦ Disjoint (f i).support (f j).support) :
    (⨆ i, f i).IsMatching := by
  intro v hv
  obtain ⟨i , hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w , hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i' , hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd heq
    simp only [Set.disjoint_left] at this
    simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, hi'⟩] using @this v

lemma IsMatching.subgraphOfAdj (h : G.Adj v w) : (G.subgraphOfAdj h).IsMatching := by
  intro _ hv
  rw [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

lemma IsMatching.coeSubgraph {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching) :
    M.coeSubgraph.IsMatching := by
  intro _ hv
  obtain ⟨w, hw⟩ := hM <| Set.mem_of_mem_image_val <| M.verts_coeSubgraph.symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp <| M.verts_coeSubgraph.symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists_const]
    exact ⟨hv.2 ▸ v.2, hw.1⟩
  · obtain ⟨_, hw', hvw⟩ := (coeSubgraph_adj _ _ _).mp hy
    rw [← hw.2 ⟨y, hw'⟩ hvw]

lemma IsMatching.exists_of_disjoint_sets_of_equiv {s t : Set V} (h : Disjoint s t)
    (f : s ≃ t) (hadj : ∀ v : s, G.Adj v (f v)) :
    ∃ M : Subgraph G, M.verts = s ∪ t ∧ M.IsMatching := by
  use {
    verts := s ∪ t
    Adj := fun v w ↦ (∃ h : v ∈ s, f ⟨v, h⟩ = w) ∨ (∃ h : w ∈ s, f ⟨w, h⟩ = v)
    adj_sub := by
      intro v w h
      obtain (⟨hv, rfl⟩ | ⟨hw, rfl⟩) := h
      · exact hadj ⟨v, _⟩
      · exact (hadj ⟨w, _⟩).symm
    edge_vert := by aesop }

  simp only [Subgraph.IsMatching, Set.mem_union, true_and]
  intro v hv
  cases' hv with hl hr
  · use f ⟨v, hl⟩
    simp only [hl, exists_const, true_or, exists_true_left, true_and]
    rintro y (rfl | ⟨hys, rfl⟩)
    · rfl
    · exact (h.ne_of_mem hl (f ⟨y, hys⟩).coe_prop rfl).elim
  · use f.symm ⟨v, hr⟩
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_prop, exists_const, or_true,
      true_and]
    rintro y (⟨hy, rfl⟩ | ⟨hy, rfl⟩)
    · exact (h.ne_of_mem hy hr rfl).elim
    · simp

protected lemma IsMatching.map {G' : SimpleGraph W} {M : Subgraph G} (f : G →g G')
    (hf : Injective f) (hM : M.IsMatching) : (M.map f).IsMatching := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv'⟩ := hM hv
  use f v'
  refine ⟨⟨v, v', hv'.1, rfl, rfl⟩, ?_⟩
  rintro _ ⟨w, w', hw, hw', rfl⟩
  cases hf hw'.symm
  rw [hv'.2 w' hw]

@[simp]
lemma Iso.isMatching_map {G' : SimpleGraph W} {M : Subgraph G} (f : G ≃g G') :
    (M.map f.toHom).IsMatching ↔ M.IsMatching where
   mp h := by simpa [← map_comp] using h.map f.symm.toHom f.symm.injective
   mpr := .map f.toHom f.injective

/--
The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def IsPerfectMatching (M : G.Subgraph) : Prop := M.IsMatching ∧ M.IsSpanning

theorem IsMatching.support_eq_verts (h : M.IsMatching) : M.support = M.verts := by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩

theorem isMatching_iff_forall_degree [∀ v, Fintype (M.neighborSet v)] :
    M.IsMatching ↔ ∀ v : V, v ∈ M.verts → M.degree v = 1 := by
  simp only [degree_eq_one_iff_unique_adj, IsMatching]

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

theorem isPerfectMatching_iff : M.IsPerfectMatching ↔ ∀ v, ∃! w, M.Adj v w := by
  refine ⟨?_, fun hm => ⟨fun v _ => hm v, fun v => ?_⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw

theorem isPerfectMatching_iff_forall_degree [∀ v, Fintype (M.neighborSet v)] :
    M.IsPerfectMatching ↔ ∀ v, M.degree v = 1 := by
  simp [degree_eq_one_iff_unique_adj, isPerfectMatching_iff]

theorem IsPerfectMatching.even_card [Fintype V] (h : M.IsPerfectMatching) :
    Even (Fintype.card V) := by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1

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

@[simp]
lemma IsPerfectMatching.toSubgraph_iff (h : M.spanningCoe ≤ G') :
    (G'.toSubgraph M.spanningCoe h).IsPerfectMatching ↔ M.IsPerfectMatching := by
  simp only [isPerfectMatching_iff, toSubgraph_adj, spanningCoe_adj]

end Subgraph

namespace ConnectedComponent

section Finite

lemma even_card_of_isPerfectMatching [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : ConnectedComponent G) (hM : M.IsPerfectMatching) :
    Even (Fintype.card c.supp) := by
  #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
  some instances that use the chain of coercions
  `[SetLike X], X → Set α → Sort _` are
  blocked by the discrimination tree. This can be fixed by redeclaring the instance for `X`
  using the double coercion but the proper fix seems to avoid the double coercion. -/
  letI : DecidablePred fun x ↦ x ∈ (M.induce c.supp).verts := fun a ↦ G.instDecidableMemSupp c a
  simpa using (hM.induce_connectedComponent_isMatching c).even_card

lemma odd_matches_node_outside [Finite V] {u : Set V}
    {c : ConnectedComponent (Subgraph.deleteVerts ⊤ u).coe}
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
  apply Nat.not_even_iff_odd.2 codd
  haveI : Fintype ↑(Subgraph.induce M (Subtype.val '' supp c)).verts := Fintype.ofFinite _
  classical
  have hMeven := Subgraph.IsMatching.even_card hMmatch
  haveI : Fintype (c.supp) := Fintype.ofFinite _
  simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.toFinset_image,
    Nat.card_eq_fintype_card, Set.toFinset_image,
    Finset.card_image_of_injective _ (Subtype.val_injective), Set.toFinset_card] at hMeven ⊢
  exact hMeven

end Finite
end ConnectedComponent

/--
A graph is matching free if it has no perfect matching. It does not make much sense to
consider a graph being free of just matchings, because any non-trivial graph has those.
-/
def IsMatchingFree (G : SimpleGraph V) := ∀ M : Subgraph G, ¬ M.IsPerfectMatching

lemma IsMatchingFree.mono {G G' : SimpleGraph V} (h : G ≤ G') (hmf : G'.IsMatchingFree) :
    G.IsMatchingFree := by
  intro x
  by_contra! hc
  apply hmf (x.map (SimpleGraph.Hom.ofLE h))
  refine ⟨hc.1.map_ofLE h, ?_⟩
  intro v
  simp only [Subgraph.map_verts, Hom.coe_ofLE, id_eq, Set.image_id']
  exact hc.2 v

lemma exists_maximal_isMatchingFree [Finite V] (h : G.IsMatchingFree) :
    ∃ Gmax : SimpleGraph V, G ≤ Gmax ∧ Gmax.IsMatchingFree ∧
      ∀ G', G' > Gmax → ∃ M : Subgraph G', M.IsPerfectMatching := by
  simp_rw [← @not_forall_not _ Subgraph.IsPerfectMatching]
  obtain ⟨Gmax, hGmax⟩ := Finite.exists_le_maximal h
  exact ⟨Gmax, ⟨hGmax.1, ⟨hGmax.2.prop, fun _ h' ↦ hGmax.2.not_prop_of_gt h'⟩⟩⟩

/-- A graph `G` consists of a set of cycles, if each vertex is either isolated or connected to
exactly two vertices. This is used to create new matchings by taking the `symmDiff` with cycles.
The definition of `symmDiff` that makes sense is the one for `SimpleGraph`. The `symmDiff`
for `SimpleGraph.Subgraph` deriving from the lattice structure also affects the vertices included,
which we do not want in this case. This is why this property is defined for `SimpleGraph`, rather
than `SimpleGraph.Subgraph`.
-/
def IsCycles (G : SimpleGraph V) := ∀ ⦃v⦄, (G.neighborSet v).Nonempty → (G.neighborSet v).ncard = 2

/--
Given a vertex with one edge in a graph of cycles this gives the other edge incident
to the same vertex.
-/
lemma IsCycles.other_adj_of_adj (h : G.IsCycles) (hadj : G.Adj v w) :
    ∃ w', w ≠ w' ∧ G.Adj v w' := by
  simp_rw [← SimpleGraph.mem_neighborSet] at hadj ⊢
  have := h ⟨w, hadj⟩
  obtain ⟨w', hww'⟩ := (G.neighborSet v).exists_ne_of_one_lt_ncard (by omega) w
  exact ⟨w', ⟨hww'.2.symm, hww'.1⟩⟩

lemma IsCycles.induce_supp (c : G.ConnectedComponent) (h : G.IsCycles) :
    (G.induce c.supp).spanningCoe.IsCycles := by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet, c.adj_spanningCoe_induce_supp] at hw
  rw [← h ⟨w, hw.2⟩]
  congr
  ext w'
  simp only [mem_neighborSet, c.adj_spanningCoe_induce_supp, hw, true_and]

open scoped symmDiff

lemma Subgraph.IsPerfectMatching.symmDiff_isCycles
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (M.spanningCoe ∆ M'.spanningCoe).IsCycles := by
  intro v
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  obtain ⟨w', hw'⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def, Set.ncard_eq_two, ne_eq, imp_iff_not_or, Set.not_nonempty_iff_eq_empty,
    Set.eq_empty_iff_forall_not_mem, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, sdiff_adj,
    spanningCoe_adj, not_or, not_and, not_not]
  by_cases hww' : w = w'
  · simp_all [← imp_iff_not_or, hww']
  · right
    use w, w'
    aesop

/--
A graph `G` is alternating with respect to some other graph `G'`, if exactly every other edge in
`G` is in `G'`. Note that the degree of each vertex needs to be at most 2 for this to be
possible. This property is used to create new matchings using `symmDiff`.
The definition of `symmDiff` that makes sense is the one for `SimpleGraph`. The `symmDiff`
for `SimpleGraph.Subgraph` deriving from the lattice structure also affects the vertices included,
which we do not want in this case. This is why this property, just like `IsCycles`, is defined
for `SimpleGraph` rather than `SimpleGraph.Subgraph`.
-/
def IsAlternating (G G' : SimpleGraph V) :=
  ∀ ⦃v w w': V⦄, w ≠ w' → G.Adj v w → G.Adj v w' → (G'.Adj v w ↔ ¬ G'.Adj v w')

lemma IsAlternating.mono {G'' : SimpleGraph V} (halt : G.IsAlternating G') (h : G'' ≤ G) :
    G''.IsAlternating G' := fun _ _ _ hww' hvw hvw' ↦ halt hww' (h hvw) (h hvw')

lemma IsPerfectMatching.symmDiff_of_isAlternating (hM : M.IsPerfectMatching)
    (hG' : G'.IsAlternating M.spanningCoe) (hG'cyc : G'.IsCycles) :
    (⊤ : Subgraph (M.spanningCoe ∆ G')).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  simp only [toSubgraph_adj, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj]
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  by_cases h : G'.Adj v w
  · obtain ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj h
    have hmadj :  M.Adj v w ↔ ¬M.Adj v w' := by simpa using hG' hw'.1 h hw'.2
    use w'
    simp only [Subgraph.top_adj, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj, hmadj.mp hw.1, hw'.2,
      not_true_eq_false, and_self, not_false_eq_true, or_true, true_and]
    rintro y (hl | hr)
    · aesop
    · obtain ⟨w'', hw''⟩ := hG'cyc.other_adj_of_adj hr.1
      by_contra! hc
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' from by simpa using hG' hc hr.1 hw'.2]
  · use w
    simp only [Subgraph.top_adj, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj, hw.1, h,
      not_false_eq_true, and_self, not_true_eq_false, or_false, true_and]
    rintro y (hl | hr)
    · exact hw.2 _ hl.1
    · have ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj hr.1
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' from by simpa using hG' hw'.1 hr.1 hw'.2]

lemma IsPerfectMatching.isAlternating_symmDiff_left {M' : Subgraph G'}
    (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  obtain ⟨v1, hm1, hv1⟩ := hM.1 (hM.2 v)
  obtain ⟨v2, hm2, hv2⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def] at *
  aesop

lemma IsPerfectMatching.isAlternating_symmDiff_right
    {M' : Subgraph G'} (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M'.spanningCoe := by
  simpa [symmDiff_comm] using isAlternating_symmDiff_left hM' hM

end SimpleGraph
