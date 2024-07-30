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

namespace SimpleGraph

universe u v
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

instance {H : G.Subgraph} : Coe H.Connected H.coe.Connected := ⟨Connected.coe⟩

instance {H : G.Subgraph} : CoeFun H.Connected (fun _ => ∀ u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩

protected lemma connected_iff' {H : G.Subgraph} :
    H.Connected ↔ H.coe.Connected := ⟨fun ⟨h⟩ => h, .mk⟩

protected lemma connected_iff {H : G.Subgraph} :
    H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty := by
  rw [H.connected_iff', connected_iff, H.preconnected_iff, Set.nonempty_coe_sort]

protected lemma Connected.preconnected {H : G.Subgraph} (h : H.Connected) : H.Preconnected := by
  rw [H.connected_iff] at h; exact h.1

protected lemma Connected.nonempty {H : G.Subgraph} (h : H.Connected) : H.verts.Nonempty := by
  rw [H.connected_iff] at h; exact h.2

theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [singletonSubgraph_verts, Set.mem_singleton_iff] at ha hb
  subst_vars
  rfl

@[simp]
theorem subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first | rfl | (apply Adj.reachable; simp)

lemma top_induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v}).Connected := by
  rw [← subgraphOfAdj_eq_induce huv]
  exact subgraphOfAdj_connected huv

@[mono]
protected lemma Connected.mono {H H' : G.Subgraph} (hle : H ≤ H') (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  refine ⟨h.coe.mono ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  exact hle.2 hvw

protected lemma Connected.mono' {H H' : G.Subgraph}
    (hle : ∀ v w, H.Adj v w → H'.Adj v w) (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  exact h.mono ⟨hv.le, hle⟩ hv

protected lemma Connected.sup {H K : G.Subgraph}
    (hH : H.Connected) (hK : K.Connected) (hn : (H ⊓ K).verts.Nonempty) :
    (H ⊔ K).Connected := by
  rw [Subgraph.connected_iff', connected_iff_exists_forall_reachable]
  obtain ⟨u, hu, hu'⟩ := hn
  exists ⟨u, Or.inl hu⟩
  rintro ⟨v, (hv|hv)⟩
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H ≤ H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
  · exact Reachable.map (Subgraph.inclusion (le_sup_right : K ≤ H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩)
end Subgraph

/-! ### Walks as subgraphs -/

namespace Walk

variable {u v w : V}

/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp]
protected def toSubgraph {u v : V} : G.Walk u v → G.Subgraph
  | nil => G.singletonSubgraph u
  | cons h p => G.subgraphOfAdj h ⊔ p.toSubgraph

theorem toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) :
    (cons h nil).toSubgraph = G.subgraphOfAdj h := by simp

theorem mem_verts_toSubgraph (p : G.Walk u v) : w ∈ p.toSubgraph.verts ↔ w ∈ p.support := by
  induction' p with _ x y z h p' ih
  · simp
  · have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp (config := { contextual := true })⟩
    simp [ih, or_assoc, this]

lemma start_mem_verts_toSubgraph (p : G.Walk u v) : u ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

lemma end_mem_verts_toSubgraph (p : G.Walk u v) : v ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

@[simp]
theorem verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w ∈ p.support } :=
  Set.ext fun _ => p.mem_verts_toSubgraph

theorem mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} :
    e ∈ p.toSubgraph.edgeSet ↔ e ∈ p.edges := by induction p <;> simp [*]

@[simp]
theorem edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSet = { e | e ∈ p.edges } :=
  Set.ext fun _ => p.mem_edges_toSubgraph

@[simp]
theorem toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := by induction p <;> simp [*, sup_assoc]

@[simp]
theorem toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph := by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]

@[simp]
theorem toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).toSubgraph = c.toSubgraph := by
  rw [rotate, toSubgraph_append, sup_comm, ← toSubgraph_append, take_spec]

@[simp]
theorem toSubgraph_map (f : G →g G') (p : G.Walk u v) :
    (p.map f).toSubgraph = p.toSubgraph.map f := by induction p <;> simp [*, Subgraph.map_sup]

@[simp]
theorem finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet w).Finite := by
  induction p with
  | nil =>
    rw [Walk.toSubgraph, neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph, Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
    apply Set.toFinite

lemma toSubgraph_le_induce_support (p : G.Walk u v) :
    p.toSubgraph ≤ (⊤ : G.Subgraph).induce {v | v ∈ p.support} := by
  convert Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm

end Walk

namespace Subgraph
lemma _root_.SimpleGraph.Walk.toSubgraph_connected {u v : V} (p : G.Walk u v) :
    p.toSubgraph.Connected := by
  induction p with
  | nil => apply singletonSubgraph_connected
  | @cons _ w _ h p ih =>
    apply (subgraphOfAdj_connected h).sup ih
    exists w
    simp

lemma induce_union_connected {H : G.Subgraph} {s t : Set V}
    (sconn : (H.induce s).Connected) (tconn : (H.induce t).Connected)
    (sintert : (s ⊓ t).Nonempty) :
    (H.induce (s ∪ t)).Connected := by
  refine (sconn.sup tconn sintert).mono ?_ ?_
  · apply le_induce_union
  · simp

lemma Connected.adj_union {H K : G.Subgraph}
    (Hconn : H.Connected) (Kconn : K.Connected) {u v : V} (uH : u ∈ H.verts) (vK : v ∈ K.verts)
    (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v} ⊔ H ⊔ K).Connected := by
  refine ((top_induce_pair_connected_of_adj huv).sup Hconn ?_).sup Kconn ?_
  · exact ⟨u, by simp [uH]⟩
  · exact ⟨v, by simp [vK]⟩

lemma preconnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Preconnected ↔ ∀ {u v}, u ∈ H.verts → v ∈ H.verts → ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  constructor
  · intro hc u v hu hv
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    exists p.map (Subgraph.hom _)
    simp [coeSubgraph_le]
  · intro hw
    rw [Subgraph.preconnected_iff]
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p, h⟩ := hw hu hv
    exact Reachable.map (Subgraph.inclusion h)
      (p.toSubgraph_connected ⟨_, p.start_mem_verts_toSubgraph⟩ ⟨_, p.end_mem_verts_toSubgraph⟩)

lemma connected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Connected ↔
      H.verts.Nonempty ∧
        ∀ {u v}, u ∈ H.verts → v ∈ H.verts → ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  rw [H.connected_iff, preconnected_iff_forall_exists_walk_subgraph, and_comm]

end Subgraph

section induced_subgraphs

lemma connected_induce_iff {s : Set V} :
    (G.induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected := by
  rw [induce_eq_coe_induce_top, ← Subgraph.connected_iff']

lemma induce_union_connected {s t : Set V}
    (sconn : (G.induce s).Connected) (tconn : (G.induce t).Connected)
    (sintert : (s ∩ t).Nonempty) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff] at sconn tconn ⊢
  exact Subgraph.induce_union_connected sconn tconn sintert

lemma induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    (G.induce {u, v}).Connected := by
  rw [connected_induce_iff]
  exact Subgraph.top_induce_pair_connected_of_adj huv

lemma Subgraph.Connected.induce_verts {H : G.Subgraph} (h : H.Connected) :
    (G.induce H.verts).Connected := by
  rw [connected_induce_iff]
  exact h.mono le_induce_top_verts (by exact rfl)

lemma Walk.connected_induce_support {u v : V} (p : G.Walk u v) :
    (G.induce {v | v ∈ p.support}).Connected := by
  rw [← p.verts_toSubgraph]
  exact p.toSubgraph_connected.induce_verts

lemma induce_connected_adj_union {v w : V} {s t : Set V}
    (sconn : (G.induce s).Connected) (tconn : (G.induce t).Connected)
    (hv : v ∈ s) (hw : w ∈ t) (ha : G.Adj v w) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff] at sconn tconn ⊢
  apply (sconn.adj_union tconn hv hw ha).mono
  · simp only [Set.mem_singleton_iff, sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    apply subgraphOfAdj_le_of_adj
    simp [hv, hw, ha]
  · simp only [Set.mem_singleton_iff, sup_le_iff, Subgraph.verts_sup, Subgraph.induce_verts]
    rw [Set.union_assoc]
    simp [Set.insert_subset_iff, Set.singleton_subset_iff, hv, hw]

lemma induce_connected_of_patches {s : Set V} (u : V) (hu : u ∈ s)
    (patches : ∀ {v}, v ∈ s → ∃ s' ⊆ s, ∃ (hu' : u ∈ s') (hv' : v ∈ s'),
                  (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩) : (G.induce s).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  exact uv.map (induceHomOfLE _ svs).toHom

lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : Set (Set V)} (Sn : S.Nonempty)
    (Snd : ∀ {s t}, s ∈ S → t ∈ S → (s ∩ t).Nonempty)
    (Sc : ∀ {s}, s ∈ S → (G.induce s).Connected) :
    (G.induce (⋃₀ S)).Connected := by
  obtain ⟨s, sS⟩ := Sn
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  rintro w hw
  simp only [Set.mem_sUnion, exists_prop] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s ∪ t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_of_mem tS),
          Or.inl vs, Or.inr wt, induce_union_connected (Sc sS) (Sc tS) (Snd sS tS) _ _⟩

lemma extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty) :
    ∃ (t' : Finset V), t ⊆ t' ∧ (G.induce (t' : Set V)).Connected := by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset, exists_prop]
    exact ⟨v, vt, Walk.end_mem_support _⟩
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

end induced_subgraphs

end SimpleGraph
