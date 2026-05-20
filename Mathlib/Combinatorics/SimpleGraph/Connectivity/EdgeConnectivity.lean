/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Set.Card

/-!
# Edge Connectivity

This file defines k-edge-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsEdgeReachable`: Two vertices are `k`-edge-reachable if they remain reachable after
  removing strictly fewer than `k` edges.
* `SimpleGraph.IsEdgeConnected`: A graph is `k`-edge-connected if any two vertices are
  `k`-edge-reachable.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v w x y : V}

variable (G k u v) in
/-- Two vertices are `k`-edge-reachable if they remain reachable after removing strictly fewer than
`k` edges. -/
def IsEdgeReachable : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v

variable (G k) in
/-- A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable. -/
def IsEdgeConnected : Prop := ∀ u v, G.IsEdgeReachable k u v

@[refl, simp]
protected lemma IsEdgeReachable.rfl {u : V} : G.IsEdgeReachable k u u := fun _ _ ↦ .rfl

protected lemma IsEdgeReachable.refl (u : V) : G.IsEdgeReachable k u u := .rfl

@[symm]
lemma IsEdgeReachable.symm (h : G.IsEdgeReachable k u v) : G.IsEdgeReachable k v u :=
  fun _ hk ↦ (h hk).symm

lemma isEdgeReachable_comm : G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u :=
  ⟨.symm, .symm⟩

@[trans]
lemma IsEdgeReachable.trans (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w) :
    G.IsEdgeReachable k u w := fun _ hk ↦ (h1 hk).trans (h2 hk)

@[gcongr]
lemma IsEdgeReachable.mono (hGH : G ≤ H) (h : G.IsEdgeReachable k u v) : H.IsEdgeReachable k u v :=
  fun _ hk ↦ h hk |>.mono <| deleteEdges_mono hGH

@[gcongr]
lemma IsEdgeReachable.anti (hkl : k ≤ l) (h : G.IsEdgeReachable l u v) : G.IsEdgeReachable k u v :=
  fun _ hk ↦ h <| by grw [← hkl]; exact hk

@[simp]
protected lemma IsEdgeReachable.zero : G.IsEdgeReachable 0 u v := by simp [IsEdgeReachable]

@[simp] protected lemma IsEdgeConnected.zero : G.IsEdgeConnected 0 := fun _ _ ↦ .zero

@[simp]
lemma isEdgeReachable_one : G.IsEdgeReachable 1 u v ↔ G.Reachable u v := by
  simp [IsEdgeReachable, ENat.lt_one_iff_eq_zero]

@[simp]
lemma isEdgeConnected_one : G.IsEdgeConnected 1 ↔ G.Preconnected := by
  simp [IsEdgeConnected, Preconnected]

lemma IsEdgeReachable.reachable (hk : k ≠ 0) (huv : G.IsEdgeReachable k u v) : G.Reachable u v :=
  isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[nontriviality]
lemma IsEdgeReachable.of_subsingleton [Subsingleton V] : G.IsEdgeReachable k u v :=
  fun _ _ ↦ .of_subsingleton

@[nontriviality]
lemma IsEdgeConnected.of_subsingleton [Subsingleton V] : G.IsEdgeConnected k :=
  fun _ _ ↦ .of_subsingleton

lemma IsEdgeConnected.preconnected (hk : k ≠ 0) (h : G.IsEdgeConnected k) : G.Preconnected :=
  fun u v ↦ (h u v).reachable hk

lemma IsEdgeConnected.connected [Nonempty V] (hk : k ≠ 0) (h : G.IsEdgeConnected k) :
    G.Connected where
  preconnected := h.preconnected hk

lemma IsEdgeReachable.le_degree [Fintype (G.neighborSet u)] (h : G.IsEdgeReachable k u v)
    (huv : u ≠ v) : k ≤ G.degree u := by
  classical
  by_contra! hh
  obtain ⟨w, _⟩ :=
    @h (G.incidenceSet u) (by simpa [← Set.coe_fintypeCard, ENat.coe_lt_coe]) |>.exists_isPath
  simpa using w.adj_snd <| by grind [Walk.nil_iff_length_eq, Walk.eq_of_length_eq_zero]

lemma IsEdgeConnected.le_degree [Fintype (G.neighborSet u)] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k ≤ G.degree u := by
  obtain ⟨v, hv⟩ := exists_ne u
  exact (h u v).le_degree hv.symm

lemma isEdgeReachable_add_one (hk : k ≠ 0) :
    G.IsEdgeReachable (k + 1) u v ↔ ∀ e, (G.deleteEdges {e}).IsEdgeReachable k u v := by
  refine ⟨fun h e s hk ↦ ?_, fun h s hs ↦ ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
    exact ENat.add_lt_add_iff_right ENat.one_ne_top |>.mpr hk
  obtain rfl | ⟨e, he⟩ := s.eq_empty_or_nonempty
  · simpa using (h s(u, u)).reachable hk
  · rw [← Set.insert_diff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
    refine h e <| ENat.add_lt_add_iff_right ENat.one_ne_top |>.mp ?_
    rwa [Set.encard_diff_singleton_add_one he]

lemma isEdgeConnected_add_one (hk : k ≠ 0) :
    G.IsEdgeConnected (k + 1) ↔ ∀ e, (G.deleteEdges {e}).IsEdgeConnected k := by
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_comm (α := Sym2 _)]

/-- An edge is a bridge iff its endpoints are adjacent and not 2-edge-reachable. -/
lemma isBridge_iff_adj_and_not_isEdgeConnected_two {u v : V} :
    G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬G.IsEdgeReachable 2 u v := by
  refine ⟨fun h ↦ ⟨h.left, fun hc ↦ ?_⟩, fun ⟨hadj, hc⟩ ↦ ?_⟩
  · exact isBridge_iff.mp h |>.right <| hc <| Set.encard_singleton _ |>.trans_lt Nat.one_lt_ofNat
  · refine isBridge_iff.mpr ⟨hadj, fun hr ↦ hc fun s hs₂ ↦ ?_⟩
    by_cases! hs₁ : s.encard ≠ (1 : ℕ)
    · apply G.isEdgeReachable_one.mpr hadj.reachable
      exact lt_of_le_of_ne (ENat.lt_coe_add_one_iff.mp hs₂) hs₁
    obtain ⟨x, rfl⟩ := Set.encard_eq_one (s := s).mp hs₁
    by_cases hx : s(u, v) = x
    · exact hx ▸ hr
    exact deleteEdges_adj.mpr ⟨hadj, hx⟩ |>.reachable

/-- A finite graph in which every vertex has even degree has no bridge. -/
theorem not_isBridge_of_even_degree [Fintype V] [DecidableRel G.Adj]
    (hG : ∀ v, Even (G.degree v)) {e : Sym2 V} : ¬ G.IsBridge e := by
  classical
  cases e with
  | h u v =>
    rw [isBridge_iff]
    rintro ⟨huv, hb⟩
    let H := G.deleteEdges {s(u, v)}
    let C : H.ConnectedComponent := H.connectedComponentMk u
    have huC : u ∈ C := by rfl
    have hvC : v ∉ C := by
      intro hv
      exact hb <| C.reachable_of_mem_supp huC hv
    let uC : C := ⟨u, huC⟩
    have degree_toSimpleGraph (D : H.ConnectedComponent) (x : D) :
        D.toSimpleGraph.degree x = H.degree (x : V) := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      exact Fintype.card_congr
        { toFun := fun y ↦ ⟨(y : D), y.prop⟩
          invFun := fun y ↦ ⟨⟨y, (D.mem_supp_congr_adj y.prop).mp x.prop⟩, y.prop⟩
          left_inv := by
            intro y
            ext
            rfl
          right_inv := by
            intro y
            ext
            rfl }
    have hH_degree_u : H.degree u = G.degree u - 1 := by
      rw [← card_neighborSet_eq_degree]
      calc
        Fintype.card (H.neighborSet u) = Fintype.card {w // G.Adj u w ∧ w ≠ v} := by
          exact Fintype.card_congr
            { toFun := fun w ↦
                ⟨w, by
                  have hwH : H.Adj u (w : V) := w.prop
                  have hw : G.Adj u w ∧ s(u, (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) := by
                    simpa [H] using hwH
                  refine ⟨hw.1, ?_⟩
                  intro hwv
                  exact hw.2 (by simp [hwv])⟩
              invFun := fun w ↦
                ⟨w, by
                  have hnot : s(u, (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) := by
                    rw [Set.mem_singleton_iff, Sym2.eq_iff]
                    rintro (h | h)
                    · exact w.2.2 h.2
                    · exact huv.ne h.1
                  change H.Adj u (w : V)
                  simpa [H] using
                    (show G.Adj u (w : V) ∧
                        s(u, (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) from ⟨w.2.1, hnot⟩)
                ⟩
              left_inv := by
                intro w
                ext
                rfl
              right_inv := by
                intro w
                ext
                rfl }
        _ = #(G.neighborFinset u \ {v}) := by
          rw [Fintype.card_of_subtype (G.neighborFinset u \ {v})]
          intro w
          simp
        _ = G.degree u - 1 := by
          rw [card_sdiff_of_subset]
          · simp
          · simp [huv]
    have hdegree_u : C.toSimpleGraph.degree uC = G.degree u - 1 := by
      rw [degree_toSimpleGraph C uC, hH_degree_u]
    have hodd_u : Odd (C.toSimpleGraph.degree uC) := by
      rw [hdegree_u]
      exact Nat.Even.sub_odd (by simpa using huv.degree_pos_left) (hG u) odd_one
    have hdegree_ne (x : C) (hx : x ≠ uC) : C.toSimpleGraph.degree x = G.degree (x : V) := by
      rw [degree_toSimpleGraph C x]
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      exact Fintype.card_congr
        { toFun := fun w ↦
            ⟨w, by
              have hwH : H.Adj (x : V) (w : V) := w.prop
              have hw : G.Adj (x : V) w ∧
                  s((x : V), (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) := by
                simpa [H] using hwH
              exact hw.1⟩
          invFun := fun w ↦
            ⟨w, by
              have hx_ne_u : (x : V) ≠ u := by
                intro hxu
                exact hx <| Subtype.ext hxu
              have hx_ne_v : (x : V) ≠ v := by
                intro hxv
                exact hvC (hxv ▸ x.prop)
              have hnot : s((x : V), (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) := by
                rw [Set.mem_singleton_iff, Sym2.eq_iff]
                rintro (h | h)
                · exact hx_ne_u h.1
                · exact hx_ne_v h.1
              change H.Adj (x : V) (w : V)
              simpa [H] using
                (show G.Adj (x : V) (w : V) ∧
                    s((x : V), (w : V)) ∉ ({s(u, v)} : Set (Sym2 V)) from ⟨w.2, hnot⟩)
            ⟩
          left_inv := by
            intro w
            ext
            rfl
          right_inv := by
            intro w
            ext
            rfl }
    rcases C.toSimpleGraph.exists_ne_odd_degree_of_exists_odd_degree uC hodd_u with
      ⟨x, hx_ne, hx_odd⟩
    have hx_even : Even (C.toSimpleGraph.degree x) := by
      rw [hdegree_ne x hx_ne]
      exact hG x
    exact (Nat.not_even_iff_odd.mpr hx_odd) hx_even

lemma isEdgeReachable_two : G.IsEdgeReachable 2 u v ↔ ∀ e, (G.deleteEdges {e}).Reachable u v := by
  simp [isEdgeReachable_add_one]

/-- A graph is 2-edge-connected iff it has no bridge. -/
-- TODO: This should be `G.IsEdgeConnected 2 ↔ ∀ e, ¬G.IsBridge e` after
-- https://github.com/leanprover-community/mathlib4/pull/32583
lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ ∀ e, (G.deleteEdges {e}).Preconnected := by
  simp [isEdgeConnected_add_one]

lemma exists_adj_isEdgeReachable_two (hne : u ≠ v) (h : G.IsEdgeReachable 2 u v) :
    ∃ w : V, G.Adj u w ∧ G.IsEdgeReachable 2 u w := by
  obtain ⟨w, hw⟩ := h.reachable (by simp) |>.exists_isPath
  have : G.Adj u w.snd := Walk.adj_snd (by grind [Walk.not_nil_of_ne])
  refine ⟨w.snd, this, fun s hs ↦ ?_⟩
  by_cases! h' : s = {s(u, w.snd)}
  · subst h'
    refine Reachable.trans (h hs) <| w.tail.toDeleteEdge _ (fun hh ↦ ?_) |>.reachable.symm
    have := hw.tail.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hh)
    simp only [Walk.getVert_tail, Nat.reduceAdd] at this
    simpa using hw.getVert_eq_start_iff_of_not_nil (Walk.not_nil_of_ne hne) |>.mp this.symm
  · refine Walk.reachable <| Walk.cons (deleteEdges_adj.mpr ⟨this, ?_⟩) Walk.nil
    contrapose h'
    refine (Set.subsingleton_iff_singleton h').mp ?_
    exact Set.encard_le_one_iff_subsingleton.mp (Order.le_of_lt_succ hs)

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {w : G.Walk u v}

private lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : x ∈ w.support) : G.IsEdgeReachable 2 u x := by
  classical
  contrapose huy
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy ↦
    he <| (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy ↦ hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')

/-- Vertices of a trail with 2-edge reachable endpoints are 2-edge reachable. -/
lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (hx : x ∈ w.support) (hy : y ∈ w.support) :
    G.IsEdgeReachable 2 x y :=
  (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hx).symm.trans
    (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hy)

/-- A trail doesn't go through a vertex that is not 2-edge-reachable from its 2-edge-reachable
endpoints. -/
@[deprecated IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (since := "2026-04-01")]
lemma IsTrail.not_mem_edges_of_not_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : ¬ G.IsEdgeReachable 2 u x) : x ∉ w.support :=
  mt (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv) huy

/-- Vertices of a closed trail are 2-edge reachable. -/
lemma IsTrail.isEdgeReachable_two {w : G.Walk u u} (hw : w.IsTrail) (hx : x ∈ w.support)
    (hy : y ∈ w.support) : G.IsEdgeReachable 2 x y :=
  hw.isEdgeReachable_two_of_isEdgeReachable_two .rfl hx hy

end SimpleGraph.Walk
