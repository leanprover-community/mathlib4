/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!
# Connectivity of subgraphs and induced graphs

## Main definitions

* `SimpleGraph.Subgraph.Preconnected` and `SimpleGraph.Subgraph.Connected` give subgraphs
  connectivity predicates via `SimpleGraph.subgraph.coe`.

-/

set_option autoImplicit true

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}

namespace Subgraph

/-- A subgraph is preconnected if it is preconnected when coerced to be a simple graph.

Note: This is a structure to make it so one can be precise about how dot notation resolves. -/
protected structure Preconnected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Preconnected

instance {H : G.Subgraph} : Coe H.Preconnected H.coe.Preconnected := ⟨Preconnected.coe⟩

instance {H : G.Subgraph} : CoeFun H.Preconnected (fun _ => ∀ u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩

protected lemma preconnected_iff {H : G.Subgraph} :
    H.Preconnected ↔ H.coe.Preconnected := ⟨fun ⟨h⟩ => h, .mk⟩

/-- A subgraph is connected if it is connected when coerced to be a simple graph.

Note: This is a structure to make it so one can be precise about how dot notation resolves. -/
protected structure Connected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Connected
#align simple_graph.subgraph.connected SimpleGraph.Subgraph.Connected

instance {H : G.Subgraph} : Coe H.Connected H.coe.Connected := ⟨Connected.coe⟩

instance {H : G.Subgraph} : CoeFun H.Connected (fun _ => ∀ u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩

protected lemma connected_iff' {H : G.Subgraph} :
    H.Connected ↔ H.coe.Connected := ⟨fun ⟨h⟩ => h, .mk⟩

protected lemma connected_iff {H : G.Subgraph} :
    H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty := by
  rw [H.connected_iff', connected_iff, H.preconnected_iff, Set.nonempty_coe_sort]
  -- 🎉 no goals

protected lemma Connected.preconnected {H : G.Subgraph} (h : H.Connected) : H.Preconnected := by
  rw [H.connected_iff] at h; exact h.1
  -- ⊢ Subgraph.Preconnected H
                             -- 🎉 no goals

protected lemma Connected.nonempty {H : G.Subgraph} (h : H.Connected) : H.verts.Nonempty := by
  rw [H.connected_iff] at h; exact h.2
  -- ⊢ Set.Nonempty H.verts
                             -- 🎉 no goals

theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected := by
  refine ⟨⟨?_⟩⟩
  -- ⊢ Preconnected (Subgraph.coe (SimpleGraph.singletonSubgraph G v))
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  -- ⊢ Reachable (Subgraph.coe (SimpleGraph.singletonSubgraph G v)) { val := a, pro …
  simp only [singletonSubgraph_verts, Set.mem_singleton_iff] at ha hb
  -- ⊢ Reachable (Subgraph.coe (SimpleGraph.singletonSubgraph G v)) { val := a, pro …
  subst_vars
  -- ⊢ Reachable (Subgraph.coe (SimpleGraph.singletonSubgraph G b)) { val := b, pro …
  rfl
  -- 🎉 no goals
#align simple_graph.singleton_subgraph_connected SimpleGraph.Subgraph.singletonSubgraph_connected

@[simp]
theorem subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected := by
  refine ⟨⟨?_⟩⟩
  -- ⊢ Preconnected (Subgraph.coe (subgraphOfAdj G hvw))
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  -- ⊢ Reachable (Subgraph.coe (subgraphOfAdj G hvw)) { val := a, property := ha }  …
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  -- ⊢ Reachable (Subgraph.coe (subgraphOfAdj G hvw)) { val := a, property := ha✝ } …
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
  -- ⊢ Reachable (Subgraph.coe (subgraphOfAdj G hvw)) { val := a, property := ha }  …
                             -- ⊢ Reachable (Subgraph.coe (subgraphOfAdj G hvw)) { val := b, property := ha }  …
                             -- ⊢ Reachable (Subgraph.coe (subgraphOfAdj G hvw)) { val := a, property := ha }  …
    first | rfl | (apply Adj.reachable; simp)
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align simple_graph.subgraph_of_adj_connected SimpleGraph.Subgraph.subgraphOfAdj_connected

lemma top_induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v}).Connected := by
  rw [← subgraphOfAdj_eq_induce huv]
  -- ⊢ Subgraph.Connected (subgraphOfAdj G huv)
  exact subgraphOfAdj_connected huv
  -- 🎉 no goals

@[mono]
protected lemma Connected.mono {H H' : G.Subgraph} (hle : H ≤ H') (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  -- ⊢ Subgraph.Connected (copy H' H.verts hv H'.Adj (_ : H'.Adj = H'.Adj))
  refine ⟨h.coe.mono ?_⟩
  -- ⊢ Subgraph.coe H ≤ Subgraph.coe (copy H' H.verts hv H'.Adj (_ : H'.Adj = H'.Ad …
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  -- ⊢ SimpleGraph.Adj (Subgraph.coe (copy H' H.verts hv✝ H'.Adj (_ : H'.Adj = H'.A …
  exact hle.2 hvw
  -- 🎉 no goals

protected lemma Connected.mono' {H H' : G.Subgraph}
    (hle : ∀ v w, H.Adj v w → H'.Adj v w) (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  exact h.mono ⟨hv.le, hle⟩ hv
  -- 🎉 no goals

protected lemma Connected.sup {H K : G.Subgraph}
    (hH : H.Connected) (hK : K.Connected) (hn : (H ⊓ K).verts.Nonempty ) :
    (H ⊔ K).Connected := by
  rw [Subgraph.connected_iff', connected_iff_exists_forall_reachable]
  -- ⊢ ∃ v, ∀ (w : ↑(H ⊔ K).verts), Reachable (Subgraph.coe (H ⊔ K)) v w
  obtain ⟨u, hu, hu'⟩ := hn
  -- ⊢ ∃ v, ∀ (w : ↑(H ⊔ K).verts), Reachable (Subgraph.coe (H ⊔ K)) v w
  exists ⟨u, Or.inl hu⟩
  -- ⊢ ∀ (w : ↑(H ⊔ K).verts), Reachable (Subgraph.coe (H ⊔ K)) { val := u, propert …
  rintro ⟨v, (hv|hv)⟩
  -- ⊢ Reachable (Subgraph.coe (H ⊔ K)) { val := u, property := (_ : u ∈ H.verts ∨  …
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H ≤ H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
    -- 🎉 no goals
  · exact Reachable.map (Subgraph.inclusion (le_sup_right : K ≤ H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩)
    -- 🎉 no goals

lemma _root_.SimpleGraph.Walk.toSubgraph_connected {u v : V} (p : G.Walk u v) :
    p.toSubgraph.Connected := by
  induction p with
  | nil => apply singletonSubgraph_connected
  | cons h p ih =>
    apply (subgraphOfAdj_connected h).sup ih
    rename_i w _
    exists w
    simp

lemma induce_union_connected {H : G.Subgraph} {s t : Set V}
    (sconn : (H.induce s).Connected) (tconn : (H.induce t).Connected)
    (sintert : (s ⊓ t).Nonempty ) :
    (H.induce (s ∪ t)).Connected := by
  refine (sconn.sup tconn sintert).mono ?_ ?_
  -- ⊢ induce H s ⊔ induce H t ≤ induce H (s ∪ t)
  · apply le_induce_union
    -- 🎉 no goals
  · simp
    -- 🎉 no goals

lemma Connected.adj_union {H K : G.Subgraph}
    (Hconn : H.Connected) (Kconn : K.Connected) {u v : V} (uH : u ∈ H.verts) (vK : v ∈ K.verts)
    (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v} ⊔ H ⊔ K).Connected := by
  refine ((top_induce_pair_connected_of_adj huv).sup Hconn ?_).sup Kconn ?_
  -- ⊢ Set.Nonempty (induce ⊤ {u, v} ⊓ H).verts
  · exact ⟨u, by simp [uH]⟩
    -- 🎉 no goals
  · exact ⟨v, by simp [vK]⟩
    -- 🎉 no goals

lemma preconnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Preconnected ↔ ∀ {u v}, u ∈ H.verts → v ∈ H.verts → ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  constructor
  -- ⊢ Subgraph.Preconnected H → ∀ {u v : V}, u ∈ H.verts → v ∈ H.verts → ∃ p, Walk …
  · intro hc u v hu hv
    -- ⊢ ∃ p, Walk.toSubgraph p ≤ H
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    -- ⊢ ∃ p, Walk.toSubgraph p ≤ H
    exists p.map (Subgraph.hom _)
    -- ⊢ Walk.toSubgraph (Walk.map (Subgraph.hom H) p) ≤ H
    simp [coeSubgraph_le]
    -- 🎉 no goals
  · intro hw
    -- ⊢ Subgraph.Preconnected H
    rw [Subgraph.preconnected_iff]
    -- ⊢ Preconnected (Subgraph.coe H)
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    -- ⊢ Reachable (Subgraph.coe H) { val := u, property := hu } { val := v, property …
    obtain ⟨p, h⟩ := hw hu hv
    -- ⊢ Reachable (Subgraph.coe H) { val := u, property := hu } { val := v, property …
    exact Reachable.map (Subgraph.inclusion h)
      (p.toSubgraph_connected ⟨_, p.start_mem_verts_toSubgraph⟩ ⟨_, p.end_mem_verts_toSubgraph⟩)

lemma connected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Connected ↔ H.verts.Nonempty ∧ ∀ {u v}, u ∈ H.verts → v ∈ H.verts →
                                        ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  rw [H.connected_iff, preconnected_iff_forall_exists_walk_subgraph, and_comm]
  -- 🎉 no goals

end Subgraph

section induced_subgraphs

lemma connected_induce_iff : (G.induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected := by
  rw [induce_eq_coe_induce_top, ← Subgraph.connected_iff']
  -- 🎉 no goals

lemma induce_union_connected {s t : Set V}
    (sconn : (G.induce s).Connected) (tconn : (G.induce t).Connected)
    (sintert : (s ∩ t).Nonempty ) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff] at sconn tconn ⊢
  -- ⊢ Subgraph.Connected (Subgraph.induce ⊤ (s ∪ t))
  exact Subgraph.induce_union_connected sconn tconn sintert
  -- 🎉 no goals

lemma induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    (G.induce {u, v}).Connected := by
  rw [connected_induce_iff]
  -- ⊢ Subgraph.Connected (Subgraph.induce ⊤ {u, v})
  exact Subgraph.top_induce_pair_connected_of_adj huv
  -- 🎉 no goals

lemma Subgraph.Connected.induce_verts {H : G.Subgraph} (h : H.Connected) :
    (G.induce H.verts).Connected := by
  rw [connected_induce_iff]
  -- ⊢ Subgraph.Connected (induce ⊤ H.verts)
  exact h.mono le_induce_top_verts (by exact rfl)
  -- 🎉 no goals

lemma Walk.connected_induce_support {u v : V} (p : G.Walk u v) :
    (G.induce {v | v ∈ p.support}).Connected := by
  rw [← p.verts_toSubgraph]
  -- ⊢ Connected (induce (Walk.toSubgraph p).verts G)
  exact p.toSubgraph_connected.induce_verts
  -- 🎉 no goals

lemma induce_connected_adj_union {s t : Set V}
    (sconn : (G.induce s).Connected) (tconn : (G.induce t).Connected)
    (hv : v ∈ s) (hw : w ∈ t) (ha : G.Adj v w) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff] at sconn tconn ⊢
  -- ⊢ Subgraph.Connected (Subgraph.induce ⊤ (s ∪ t))
  apply (sconn.adj_union tconn hv hw ha).mono
  -- ⊢ Subgraph.induce ⊤ {v, w} ⊔ Subgraph.induce ⊤ s ⊔ Subgraph.induce ⊤ t ≤ Subgr …
  · simp only [Set.mem_singleton_iff, sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    apply subgraphOfAdj_le_of_adj
    -- ⊢ Subgraph.Adj (Subgraph.induce ⊤ (s ∪ t)) v w
    simp [hv, hw, ha]
    -- 🎉 no goals
  · simp only [Set.mem_singleton_iff, sup_le_iff, Subgraph.verts_sup, Subgraph.induce_verts]
    -- ⊢ {v, w} ∪ s ∪ t = s ∪ t
    rw [Set.union_assoc]
    -- ⊢ {v, w} ∪ (s ∪ t) = s ∪ t
    simp [Set.insert_subset_iff, Set.singleton_subset_iff, hv, hw]
    -- 🎉 no goals

lemma induce_connected_of_patches {s : Set V} (u : V) (hu : u ∈ s)
    (patches : ∀ {v} (_ : v ∈ s), ∃ (s' : Set V) (_ : s' ⊆ s) (hu' : u ∈ s') (hv' : v ∈ s'),
                  (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩) : (G.induce s).Connected := by
  rw [connected_iff_exists_forall_reachable]
  -- ⊢ ∃ v, ∀ (w : ↑s), Reachable (induce s G) v w
  refine ⟨⟨u, hu⟩, ?_⟩
  -- ⊢ ∀ (w : ↑s), Reachable (induce s G) { val := u, property := hu } w
  rintro ⟨v, hv⟩
  -- ⊢ Reachable (induce s G) { val := u, property := hu } { val := v, property :=  …
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  -- ⊢ Reachable (induce s G) { val := u, property := hu } { val := v, property :=  …
  exact uv.map (induceHomOfLE _ svs).toHom
  -- 🎉 no goals

lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : Set (Set V)} (Sn : S.Nonempty)
    (Snd : ∀ {s t}, s ∈ S → t ∈ S → (s ∩ t).Nonempty)
    (Sc : ∀ {s}, s ∈ S → (G.induce s).Connected) :
    (G.induce (⋃₀ S)).Connected := by
  obtain ⟨s, sS⟩ := Sn
  -- ⊢ Connected (induce (⋃₀ S) G)
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  -- ⊢ Connected (induce (⋃₀ S) G)
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  -- ⊢ ∀ {v_1 : V}, v_1 ∈ ⋃₀ S → ∃ s' x hu' hv', Reachable (induce s' G) { val := v …
  rintro w hw
  -- ⊢ ∃ s' x hu' hv', Reachable (induce s' G) { val := v, property := hu' } { val  …
  simp only [Set.mem_sUnion, exists_prop] at hw
  -- ⊢ ∃ s' x hu' hv', Reachable (induce s' G) { val := v, property := hu' } { val  …
  obtain ⟨t, tS, wt⟩ := hw
  -- ⊢ ∃ s' x hu' hv', Reachable (induce s' G) { val := v, property := hu' } { val  …
  refine ⟨s ∪ t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_of_mem tS),
          Or.inl vs, Or.inr wt, induce_union_connected (Sc sS) (Sc tS) (Snd sS tS) _ _⟩

lemma extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty) :
    ∃ (t' : Finset V), t ⊆ t' ∧ (G.induce (t' : Set V)).Connected := by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset, exists_prop]
    refine ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset, Set.mem_iUnion,
                 Set.mem_setOf_eq, Walk.start_mem_support, exists_prop, and_true]
      exact ⟨u, ut⟩
    intros v hv
    simp only [Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset, exists_prop] at hv
    obtain ⟨w, wt, hw⟩ := hv
    refine ⟨{x | x ∈ (Gpc u w).some.support}, ?_, ?_⟩
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset]
      exact fun x xw => Set.mem_iUnion₂.mpr ⟨w,wt,xw⟩
    · simp only [Set.mem_setOf_eq, Walk.start_mem_support, exists_true_left]
      refine ⟨hw, Walk.connected_induce_support _ _ _⟩
