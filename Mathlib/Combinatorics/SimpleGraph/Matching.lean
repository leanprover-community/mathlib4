/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller, Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Parity
import Mathlib.SetTheory.Cardinal.Ordinal

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

lemma IsMatching.exists_of_disjoint_sets_of_card_eq {s t : Set V} (h : Disjoint s t)
    (f : s ≃ t) (hadj : ∀ {v w : V}, v ∈ s → w ∈ t → G.Adj v w) :
    ∃ M : Subgraph G, M.verts = s ∪ t ∧ M.IsMatching := by
  haveI (v : V) : Decidable (v ∈ s) := Classical.dec _
  use {
    verts := s ∪ t
    Adj := fun v w ↦ (if h : v ∈ s then f ⟨v, h⟩ = w else False) ∨
          (if h : w ∈ s then f ⟨w, h⟩ = v else False)
    adj_sub := by
      intro v w h
      cases' h with hl hr
      · have hvs : v ∈ s := by
          simp only [dite_else_false] at hl
          obtain ⟨hv, _⟩ := hl
          exact hv
        simp only [hvs, ↓reduceDIte] at hl
        have hwt : w ∈ t := by
          rw [← hl]
          exact Subtype.coe_prop (f ⟨v, of_eq_true (eq_true hvs)⟩)
        exact hadj hvs hwt
      · have hws : w ∈ s := by
          simp only [dite_else_false] at hr
          obtain ⟨hw, _⟩ := hr
          exact hw
        simp only [hws, ↓reduceDIte] at hr
        have hvt : v ∈ t := by
          rw [← hr]
          exact Subtype.coe_prop (f ⟨w, of_eq_true (eq_true hws)⟩)
        rw [SimpleGraph.adj_comm]
        exact hadj hws hvt
    edge_vert := by
      intro v w hvw
      cases' hvw with hl hr
      · simp only [dite_else_false] at hl
        obtain ⟨hvs, _⟩ := hl
        left
        exact hvs
      · simp only [dite_else_false] at hr
        obtain ⟨_, rfl⟩ := hr
        right
        exact (f _).coe_prop
  }

  simp only [dite_else_false, true_and]
  intro v hv
  simp only [Set.mem_union] at hv
  cases' hv with hl hr
  · use f ⟨v, hl⟩
    simp only [exists_prop', nonempty_prop, and_true]
    refine ⟨by left; exact hl, ?_⟩
    intro y hy
    cases' hy with h1 h2
    · obtain ⟨_, rfl⟩ := h1; rfl
    · obtain ⟨hys, rfl⟩ := h2
      exact (h.ne_of_mem hl (f ⟨y, hys⟩).coe_prop rfl).elim
  · use f.symm ⟨v, hr⟩
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_prop, exists_const, or_true,
      true_and]
    intro y hy
    cases' hy with h1 h2
    · obtain ⟨hvs, _⟩ := h1
      exact (h.ne_of_mem hvs hr rfl).elim
    · obtain ⟨_, rfl⟩ := h2
      simp only [Subtype.coe_eta, Equiv.symm_apply_apply]

lemma Iso.isMatching_map {G' : SimpleGraph W} {M : Subgraph G} (f : SimpleGraph.Iso G G') :
    (M.map f.toHom).IsMatching ↔ M.IsMatching := by
  constructor
  · intro hM v hv
    have hfv : f v ∈ (Subgraph.map (Iso.map f G).toHom M).verts := by
      simpa [map_verts, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, Iso.map_apply,
        Set.mem_image_equiv, Equiv.symm_apply_apply] using hv
    obtain ⟨w, hw⟩ := hM hfv
    use f.symm w
    dsimp at *
    constructor
    · rw [Relation.map_apply] at hw
      obtain ⟨a, b, ⟨hab, ha, rfl⟩⟩ := hw.1
      rw [RelIso.eq_iff_eq] at ha
      subst ha
      simpa [Equiv.symm_apply_apply] using hab
    · intro y hy
      have : f y = w := by
        apply hw.2 (f y)
        rw [@Relation.map_apply]
        use v, y
      rw [← this]
      simp only [RelIso.symm_apply_apply]
  · intro hM v hv
    simp only [map_verts, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, Set.mem_image] at hv
    obtain ⟨v', ⟨hv', rfl⟩⟩ := hv
    obtain ⟨w, hw⟩ := hM hv'
    use f w
    dsimp at *
    constructor
    · have := hw.1
      apply Relation.map_apply.mpr
      use v', w
    · intro y hy
      rw [Relation.map_apply] at hy
      obtain ⟨a, b, ⟨hab, ha, rfl⟩⟩ := hy
      rw [RelIso.eq_iff_eq] at ha
      subst ha
      rw [hw.2 _ hab]

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

end Subgraph

namespace ConnectedComponent

section Finite

lemma even_card_of_isPerfectMatching [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : ConnectedComponent G) (hM : M.IsPerfectMatching) :
    Even (Fintype.card c.supp) := by
  #adaptation_note
  /--
  After lean4#5020, some instances that use the chain of coercions
  `[SetLike X], X → Set α → Sort _` are
  blocked by the discrimination tree. This can be fixed by redeclaring the instance for `X`
  using the double coercion but the proper fix seems to avoid the double coercion.
  -/
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

@[simp]
theorem disjoint_insert_left {a : V} {s t : Set V} : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]
theorem disjoint_insert_right {a : V} {s t : Set V} : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, _root_.disjoint_comm]


lemma split_set [DecidableEq V] (u : Set V) (he : Even (Nat.card u)) : ∃ (s t : Set V),
    s ∪ t = u  ∧ Disjoint s t ∧  Cardinal.mk s = Cardinal.mk t := by
  obtain hfin | hnfin := u.finite_or_infinite
  · obtain rfl | h := u.eq_empty_or_nonempty
    · use ∅, ∅
      simp only [Set.union_self, disjoint_self, Set.bot_eq_empty, Cardinal.mk_eq_zero, and_self]
    · obtain ⟨x, y, hxy⟩ := Set.Finite.two_of_even_of_nonempty hfin h he
      have hu'e := Set.Finite.even_card_diff_pair hfin he hxy.1 hxy.2.1 hxy.2.2
      obtain ⟨s, t, hst⟩ := split_set (u \ {x, y}) hu'e
      use insert x s, insert y t
      refine ⟨by simp only [Set.union_insert, Set.insert_union, hst.1,
          show u \ { x, y } = (u \ { y }) \ { x } from by
            simp only [Set.diff_diff, Set.union_singleton],
          Set.insert_diff_singleton, Set.insert_comm, hxy.2.1, Set.insert_eq_of_mem, hxy.1], ?_⟩
      have hyns : y ∉ s := fun hys ↦ by simpa [hst.1] using (Set.subset_union_left hys : y ∈ s ∪ t)
      have hxnt : x ∉ t := fun hxt ↦ by simpa [hst.1] using (Set.subset_union_right hxt : x ∈ s ∪ t)
      have hynt : y ∉ t := fun hys ↦ by simpa [hst.1] using (Set.subset_union_right hys : y ∈ s ∪ t)
      have hxns : x ∉ s := fun hxs ↦ by simpa [hst.1] using (Set.subset_union_left hxs : x ∈ s ∪ t)
      constructor <;> simp [hyns, hxnt, Cardinal.mk_insert hynt, Cardinal.mk_insert hxns, hst.2.2,
        hst.2.1, hxy.2.2.symm]
  · have f : u ⊕ u ≃ u := by
      have : Inhabited (u ⊕ u ≃ u) := by
        apply Classical.inhabited_of_nonempty
        rw [← Cardinal.eq, Cardinal.mk_sum, Cardinal.add_eq_max (by
          rw [@Cardinal.aleph0_le_lift]
          exact Cardinal.infinite_iff.mp (Set.infinite_coe_iff.mpr hnfin)
          )]
        simp only [Cardinal.lift_id, max_self]
      exact this.default
    use Subtype.val '' (f '' (Sum.inl '' Set.univ)), Subtype.val '' (f '' (Sum.inr '' Set.univ))
    constructor
    · ext v
      simp only [Set.image_univ, Set.mem_union, Set.mem_image, Set.mem_image_equiv, Set.mem_range,
        Subtype.exists, exists_and_right, exists_eq_right]
      refine ⟨fun h ↦ by
        cases' h with hl hr
        · obtain ⟨hvu, _⟩ := hl
          exact hvu
        · obtain ⟨hvu, _⟩ := hr
          exact hvu, ?_⟩
      · intro hv
        rw [← exists_or]
        use hv
        simp only [Sum.exists, Sum.inl.injEq, exists_subtype_mk_eq_iff, exists_eq, true_and,
          Subtype.exists, reduceCtorEq, exists_false, false_and, or_false, Sum.inr.injEq, false_or]
        obtain ⟨a, ha⟩ := f.surjective ⟨v, hv⟩
        rw [← ha]
        simp only [EmbeddingLike.apply_eq_iff_eq]
        cases' a with l r
        · left; use l, l.coe_prop
        · right; use r, r.coe_prop
    · constructor
      · simp only [Set.image_univ, ← Set.image_comp]
        apply Set.disjoint_image_of_injective (by
          simp only [Subtype.val_injective, Injective.of_comp_iff, f.injective])
        rw [@Set.disjoint_right]
        intro a ha
        simp only [Set.mem_range, Subtype.exists, not_exists] at *
        intro v hv
        obtain ⟨_, _, h⟩ := ha
        rw [← h]
        exact Sum.inl_ne_inr
      · simp only [Set.image_univ, Subtype.val_injective, Cardinal.mk_image_eq, f.injective,
          Sum.inl_injective, Cardinal.mk_range_eq, Sum.inr_injective]
termination_by u.ncard
decreasing_by
· simp_wf
  refine Set.ncard_lt_ncard ?_ hfin
  exact ⟨Set.diff_subset, by
    rw [Set.not_subset_iff_exists_mem_not_mem]
    use x
    exact ⟨hxy.1, by simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
      not_true_eq_false, and_false, not_false_eq_true]⟩⟩

lemma inf_set (u : Set V) (hinfin : u.Infinite) : ∃ (s t : Set V),
    s ∪ t = u  ∧ Disjoint s t ∧  Cardinal.mk s = Cardinal.mk t := by
  sorry

lemma IsClique.even_card_iff_exists_isMatching [DecidableEq V] (u : Set V)
    (hc : G.IsClique u) : Even (Nat.card u) ↔ ∃ (M : Subgraph G), M.verts = u ∧ M.IsMatching := by
  obtain hfin | hnfin := u.finite_or_infinite
  · haveI : Fintype u := hfin.fintype
    refine ⟨?_ , by
      rintro ⟨M, ⟨hMl, hMr⟩⟩
      haveI : Fintype M.verts := hMl ▸ hfin.fintype
      subst hMl
      simpa [Nat.card_eq_card_finite_toFinset hfin, Set.toFinite_toFinset,
        Set.toFinset_card] using hMr.even_card⟩
    intro he
    obtain rfl | h := u.eq_empty_or_nonempty
    · use ⊥
      simp only [Subgraph.verts_bot, true_and]
      intro _ h
      contradiction
    · obtain ⟨x, y, hxy⟩ := Set.Finite.two_of_even_of_nonempty hfin h he
      let u' := u \ {x, y}
      have hu'e := Set.Finite.even_card_diff_pair hfin he hxy.1 hxy.2.1 hxy.2.2
      have hu'c := hc.subset (Set.diff_subset : u' ⊆ u)
      obtain ⟨M, hM⟩ := (IsClique.even_card_iff_exists_isMatching u' hu'c).mp hu'e
      use M ⊔ subgraphOfAdj _ (hc hxy.1 hxy.2.1 hxy.2.2)
      simp only [Subgraph.verts_sup, hM.1, subgraphOfAdj_verts]
      refine ⟨by
        rw [Set.diff_union_self]
        exact Set.union_eq_self_of_subset_right (Set.pair_subset hxy.1 hxy.2.1), ?_⟩
      refine Subgraph.IsMatching.sup hM.2
        (Subgraph.IsMatching.subgraphOfAdj (hc hxy.left hxy.right.left hxy.right.right)) ?_
      simp only [support_subgraphOfAdj, hM.2.support_eq_verts, hM.1]
      exact Set.disjoint_sdiff_left
  · simp only [Set.Infinite.card_eq_zero hnfin, even_zero, true_iff]
    -- have : Infinite V := by
    --   rw [← @Set.infinite_univ_iff]
    --   exact Set.Infinite.mono (fun _ _ ↦ by trivial) hnfin
    -- have : V ≃ V ⊕ V := by
    --   have : Inhabited (V ≃ V ⊕ V) := by
    --     apply Classical.inhabited_of_nonempty
    --     rw [← Cardinal.eq, Cardinal.mk_sum, Cardinal.add_eq_max (by
    --       rw [@Cardinal.aleph0_le_lift]
    --       exact Cardinal.infinite_iff.mp this
    --       )]
    --     simp only [Cardinal.lift_id, max_self]
    --   exact this.default

    -- simp_rw [← Subgraph.Iso.isMatching_map (SimpleGraph.Iso.map this G)]
    obtain ⟨s, t, ⟨rfl, hst1, hst2⟩⟩ := inf_set u hnfin
    rw [Cardinal.eq] at hst2
    have f := (Classical.inhabited_of_nonempty hst2).default
    haveI (v : V) : Decidable (v ∈ s) := Classical.dec _
    use {
      verts := s ∪ t
      Adj := fun v w ↦ (if h : v ∈ s then f ⟨v, h⟩ = w else False) ∨
            (if h : w ∈ s then f ⟨w, h⟩ = v else False)
      adj_sub := by
        intro v w h
        cases' h with hl hr
        · have hvs : v ∈ s := by
            simp only [dite_else_false] at hl
            obtain ⟨hv, _⟩ := hl
            exact hv
          simp only [hvs, ↓reduceDIte] at hl
          have hwt : w ∈ t := by
            rw [← hl]
            exact Subtype.coe_prop (f ⟨v, of_eq_true (eq_true hvs)⟩)
          exact hc (Set.mem_union_left t hvs)
            (Set.mem_union_right s hwt) (Disjoint.ne_of_mem hst1 hvs hwt)
        · have hws : w ∈ s := by
            simp only [dite_else_false] at hr
            obtain ⟨hw, _⟩ := hr
            exact hw
          simp only [hws, ↓reduceDIte] at hr
          have hvt : v ∈ t := by
            rw [← hr]
            exact Subtype.coe_prop (f ⟨w, of_eq_true (eq_true hws)⟩)
          apply hc (Set.mem_union_right s hvt) (Set.mem_union_left t hws)
          rw [ne_comm]
          exact Disjoint.ne_of_mem hst1 hws hvt
      edge_vert := by
        intro v w hvw
        cases' hvw with hl hr
        · simp only [dite_else_false] at hl
          obtain ⟨hvs, _⟩ := hl
          left
          exact hvs
        · simp only [dite_else_false] at hr
          obtain ⟨_, rfl⟩ := hr
          right
          exact (f _).coe_prop
    }
    -- use {
    --   verts := s ∪ t
    --   Adj := fun v w ↦ (v ∈ s ∪ t) ∧ (w ∈ s ∪ t) ∧
    --       ((h : v ∈ s) → f ⟨v, h⟩ = w) ∧ ((h : w ∈ s) → f ⟨w, h⟩ = v)
    --   adj_sub := by
    --     intro v w h
    --     by_cases hv : v ∈ s
    --     · have hvw' : v ≠ w := by
    --         apply Disjoint.ne_of_mem hst1 hv
    --         rw [← h.2.2.1 hv]
    --         simp only [Subtype.coe_prop]
    --       exact hc h.1 h.2.1 hvw'
    --     · have hvt : v ∈ t := by
    --         cases' h.1 with hl hr
    --         · exfalso; exact hv hl
    --         · exact hr
    --       obtain ⟨w', hw', rfl⟩ : ∃ (w' : V) (hw' : w' ∈ s), f ⟨w', hw'⟩ = v := by
    --         use f.symm ⟨v, hvt⟩
    --         use (Subtype.coe_prop (f.symm ⟨v, hvt⟩))
    --         simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    --       apply hc h.1 h.2.1
    --       intro hw
    --       by_cases hws : w ∈ s
    --       · rw [hw] at hv
    --         exact hv hws
    --       · have hwt : w ∈ t := by
    --           cases' h.2.1 with hl hr
    --           · exfalso; exact hws hl
    --           · exact hr

    --         sorry
    --   edge_vert := sorry
    --   symm := sorry
    -- }
    sorry
termination_by u.ncard
decreasing_by
· simp_wf
  refine Set.ncard_lt_ncard ?_ hfin
  exact ⟨Set.diff_subset, by
    rw [Set.not_subset_iff_exists_mem_not_mem]
    use x
    exact ⟨hxy.1, by simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
      not_true_eq_false, and_false, not_false_eq_true]⟩⟩

lemma completeGraph_even_iff_exists_isMatching [DecidableEq V] :
    Even (Nat.card V) ↔ ∃ (M : Subgraph (completeGraph V)), M.verts = Set.univ ∧ M.IsMatching := by
  simpa [Set.Nat.card_coe_set_eq, Set.ncard_univ]
    using IsClique.even_card_iff_exists_isMatching (Set.univ : Set V) IsClique.completeGraph
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

end SimpleGraph
