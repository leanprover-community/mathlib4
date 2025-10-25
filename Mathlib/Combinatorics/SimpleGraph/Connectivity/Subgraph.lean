/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

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

/--
This lemma establishes a condition under which a subgraph is the same as a connected component.
Note the asymmetry in the hypothesis `h`: `v` is in `H.verts`, but `w` is not required to be.
-/
lemma Connected.exists_verts_eq_connectedComponentSupp {H : Subgraph G}
    (hc : H.Connected) (h : ∀ v ∈ H.verts, ∀ w, G.Adj v w → H.Adj v w) :
    ∃ c : G.ConnectedComponent, H.verts = c.supp := by
  rw [SimpleGraph.ConnectedComponent.exists]
  obtain ⟨v, hv⟩ := hc.nonempty
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun hw ↦ by simpa using (hc ⟨w, hw⟩ ⟨v, hv⟩).map H.hom,
    fun a ↦ a.symm.mem_subgraphVerts h hv⟩

end Subgraph

namespace ConnectedComponent

variable (C : G.ConnectedComponent)

/-- The induced subgraph of a connected component. -/
abbrev toSubgraph : G.Subgraph :=
  .induce ⊤ C.supp

@[simp]
lemma coe_toSubgraph : C.toSubgraph.coe = C.toSimpleGraph :=
  induce_eq_coe_induce_top C.supp |>.symm

@[simp]
lemma spanningCoe_toSubgraph_eq_spanningCoe_toSimpleGraph :
    C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe :=
  spanningCoe_induce_top_eq_spanningCoe_induce _

@[simp]
lemma toSubgraph_adj_eq_spanningCoe_toSimpleGraph_adj :
    C.toSubgraph.Adj = C.toSimpleGraph.spanningCoe.Adj :=
  induce_top_adj_eq_spanningCoe_induce_adj _

lemma connected_toSubgraph : C.toSubgraph.Connected :=
  ⟨C.coe_toSubgraph ▸ C.connected_toSimpleGraph⟩

end ConnectedComponent

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
  induction p with
  | nil => simp
  | cons h p' ih =>
    rename_i x y z
    have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp +contextual⟩
    simp [ih, or_assoc, this]

lemma not_nil_of_adj_toSubgraph {u v} {x : V} {p : G.Walk u v} (hadj : p.toSubgraph.Adj w x) :
    ¬p.Nil := by
  cases p <;> simp_all

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

lemma adj_toSubgraph_mapLe {G' : SimpleGraph V} {w x : V} {p : G.Walk u v} (h : G ≤ G') :
    (p.mapLe h).toSubgraph.Adj w x ↔ p.toSubgraph.Adj w x := by
  simp

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

theorem toSubgraph_adj_getVert {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    w.toSubgraph.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp only [Walk.toSubgraph, Walk.getVert_zero, zero_add, getVert_cons_succ, Subgraph.sup_adj,
        subgraphOfAdj_adj, true_or]
    · simp only [Walk.toSubgraph, getVert_cons_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_succ_iff.mp hi)

theorem toSubgraph_adj_snd {u v} (w : G.Walk u v) (h : ¬ w.Nil) : w.toSubgraph.Adj u w.snd := by
  simpa using w.toSubgraph_adj_getVert (not_nil_iff_lt_length.mp h)

theorem toSubgraph_adj_penultimate {u v} (w : G.Walk u v) (h : ¬ w.Nil) :
    w.toSubgraph.Adj w.penultimate v := by
  rw [not_nil_iff_lt_length] at h
  simpa [show w.length - 1 + 1 = w.length from by cutsat]
    using w.toSubgraph_adj_getVert (by cutsat : w.length - 1 < w.length)

theorem toSubgraph_adj_iff {u v u' v'} (w : G.Walk u v) :
    w.toSubgraph.Adj u' v' ↔ ∃ i, s(w.getVert i, w.getVert (i + 1)) =
      s(u', v') ∧ i < w.length := by
  constructor
  · intro hadj
    unfold Walk.toSubgraph at hadj
    match w with
    | .nil =>
      simp only [singletonSubgraph_adj, Pi.bot_apply, Prop.bot_eq_false] at hadj
    | .cons h p =>
      simp only [Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk] at hadj
      cases hadj with
      | inl hl =>
        use 0
        simp only [Walk.getVert_zero, zero_add, getVert_cons_succ]
        refine ⟨?_, by simp only [length_cons, Nat.zero_lt_succ]⟩
        exact Sym2.eq_iff.mpr hl
      | inr hr =>
        obtain ⟨i, hi⟩ := (toSubgraph_adj_iff _).mp hr
        use i + 1
        simp only [getVert_cons_succ]
        constructor
        · exact hi.1
        · simp only [Walk.length_cons, Nat.add_lt_add_right hi.2 1]
  · rintro ⟨i, hi⟩
    rw [← Subgraph.mem_edgeSet, ← hi.1, Subgraph.mem_edgeSet]
    exact toSubgraph_adj_getVert _ hi.2

lemma mem_support_of_adj_toSubgraph {u v u' v' : V} {p : G.Walk u v} (hp : p.toSubgraph.Adj u' v') :
    u' ∈ p.support := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hp)

namespace IsPath

lemma neighborSet_toSubgraph_startpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet u = {p.snd} := by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by simp_all⟩
  rintro ⟨i, hl | hr⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_setOf]; cutsat) (by rw [Set.mem_setOf]; cutsat)
      simp_all
    simp_all
  · have : i + 1 = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_setOf]; cutsat) (by rw [Set.mem_setOf]; cutsat)
      simp_all
    contradiction

lemma neighborSet_toSubgraph_endpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet v = {p.penultimate} := by
  simpa using IsPath.neighborSet_toSubgraph_startpoint hp.reverse
      (by rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]; exact
        Walk.not_nil_iff_lt_length.mp hnp)

lemma neighborSet_toSubgraph_internal {u} {i : ℕ} {p : G.Walk u v} (hp : p.IsPath)
    (h : i ≠ 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i from by cutsat) ▸
    p.toSubgraph_adj_getVert (by cutsat : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl, _⟩ | ⟨_, hl⟩⟩ <;>
    apply hp.getVert_injOn (by rw [Set.mem_setOf_eq]; cutsat)
      (by rw [Set.mem_setOf_eq]; cutsat) at hl <;> aesop

lemma ncard_neighborSet_toSubgraph_internal_eq_two {u} {i : ℕ} {p : G.Walk u v} (hp : p.IsPath)
    (h : i ≠ 0) (h' : i < p.length) :
    (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 := by
  rw [hp.neighborSet_toSubgraph_internal h h']
  have : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_setOf_eq]; cutsat) (by rw [Set.mem_setOf_eq]; cutsat) h
    omega
  simp_all

lemma snd_of_toSubgraph_adj {u v v'} {p : G.Walk u v} (hp : p.IsPath)
    (hadj : p.toSubgraph.Adj u v') : p.snd = v' := by
  have ⟨i, hi⟩ := p.toSubgraph_adj_iff.mp hadj
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hi
  rcases hi.1 with ⟨hl1, rfl⟩|⟨hr1, hr2⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_setOf]; cutsat) (by rw [Set.mem_setOf]; cutsat)
      rw [p.getVert_zero, hl1]
    simp [this]
  · have : i + 1 = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_setOf]; cutsat) (by rw [Set.mem_setOf]; cutsat)
      rw [p.getVert_zero, hr2]
    contradiction

end IsPath

namespace IsCycle

lemma neighborSet_toSubgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) :
    p.toSubgraph.neighborSet u = {p.snd, p.penultimate} := by
  have hadj1 := p.toSubgraph_adj_snd hpc.not_nil
  have hadj2 := (p.toSubgraph_adj_penultimate hpc.not_nil).symm
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i, hl | hr⟩
  · rw [hpc.getVert_endpoint_iff (by cutsat)] at hl
    cases hl.1 <;> aesop
  · rcases (hpc.getVert_endpoint_iff (by cutsat)).mp hr.2 with h1 | h2
    · contradiction
    · simp only [penultimate, ← h2, add_tsub_cancel_right]
      simp_all

lemma neighborSet_toSubgraph_internal {u} {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i ≠ 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i from by cutsat) ▸
    p.toSubgraph_adj_getVert (by cutsat : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl1, hl2⟩ | ⟨hr1, hr2⟩⟩
  · apply hpc.getVert_injOn' (by rw [Set.mem_setOf_eq]; cutsat)
      (by rw [Set.mem_setOf_eq]; cutsat) at hl1
    simp_all
  · apply hpc.getVert_injOn (by rw [Set.mem_setOf_eq]; cutsat)
      (by rw [Set.mem_setOf_eq]; cutsat) at hr2
    aesop

lemma ncard_neighborSet_toSubgraph_eq_two {u v} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : v ∈ p.support) : (p.toSubgraph.neighborSet v).ncard = 2 := by
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h ⊢
  obtain ⟨i, hi⟩ := h
  by_cases he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    rw [← huv, hpc.neighborSet_toSubgraph_endpoint]
    exact Set.ncard_pair hpc.snd_ne_penultimate
  push_neg at he
  rw [← hi.1, hpc.neighborSet_toSubgraph_internal he.1 (by cutsat)]
  exact Set.ncard_pair (hpc.getVert_sub_one_ne_getVert_add_one (by cutsat))

lemma exists_isCycle_snd_verts_eq {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.snd = w ∧ p'.toSubgraph.verts = p.toSubgraph.verts := by
  have : w ∈ p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  obtain hl | hr := this
  · exact ⟨p, ⟨h, hl.symm, rfl⟩⟩
  · use p.reverse
    rw [penultimate, ← getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [toSubgraph_reverse _]⟩

end IsCycle

open Finset

variable [DecidableEq V] {u v : V} {p : G.Walk u v}

/-- This lemma states that given some finite set of vertices, of which at least one is in the
support of a given walk, one of them is the first to be encountered. This consequence is encoded
as the set of vertices, restricted to those in the support, except for the first, being empty.
You could interpret this as being `takeUntilSet`, but defining this is slightly involved due to
not knowing what the final vertex is. This could be done by defining a function to obtain the
first encountered vertex and then use that to define `takeUntilSet`. That direction could be
worthwhile if this concept is used more widely. -/
lemma exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty (s : Finset V)
    (h : {x ∈ s | x ∈ p.support}.Nonempty) :
    ∃ x ∈ s, ∃ hx : x ∈ p.support, {t ∈ s.erase x | t ∈ (p.takeUntil x hx).support} = ∅ := by
  simp only [← Finset.subset_empty]
  induction hp : p.length + #s using Nat.strong_induction_on generalizing s v with | _ n ih
  simp only [Finset.Nonempty, mem_filter] at h
  obtain ⟨x, hxs, hx⟩ := h
  obtain h | h := Finset.eq_empty_or_nonempty {t ∈ s.erase x | t ∈ (p.takeUntil x hx).support}
  · use x, hxs, hx, h.le
  have : (p.takeUntil x hx).length + #(s.erase x) < n := by
    rw [← card_erase_add_one hxs] at hp
    have := p.length_takeUntil_le hx
    omega
  obtain ⟨y, hys, hyp, h⟩ := ih _ this (s.erase x) h rfl
  use y, mem_of_mem_erase hys, support_takeUntil_subset p hx hyp
  rwa [takeUntil_takeUntil, erase_right_comm, filter_erase, erase_eq_of_notMem] at h
  simp only [mem_filter, mem_erase, ne_eq, not_and, and_imp]
  rintro hxy -
  exact notMem_support_takeUntil_support_takeUntil_subset (Ne.symm hxy) hx hyp

lemma exists_mem_support_forall_mem_support_imp_eq (s : Finset V)
    (h : {x ∈ s | x ∈ p.support}.Nonempty) :
    ∃ x ∈ s, ∃ (hx : x ∈ p.support),
      ∀ t ∈ s, t ∈ (p.takeUntil x hx).support → t = x := by
  obtain ⟨x, hxs, hx, h⟩ := p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty s h
  use x, hxs, hx
  suffices {t ∈ s | t ∈ (p.takeUntil x hx).support} ⊆ {x} by simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty, ← Finset.subset_insert_iff,
    LawfulSingleton.insert_empty_eq] at h

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
  · simp only [sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    apply subgraphOfAdj_le_of_adj
    simp [hv, hw, ha]
  · simp only [Subgraph.verts_sup, Subgraph.induce_verts]
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
  simp only [Set.mem_sUnion] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s ∪ t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_of_mem tS),
          Or.inl vs, Or.inr wt, induce_union_connected (Sc sS) (Sc tS) (Snd sS tS) _ _⟩

lemma extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty) :
    ∃ (t' : Finset V), t ⊆ t' ∧ (G.induce (t' : Set V)).Connected := by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset, Set.mem_iUnion,
                 Set.mem_setOf_eq, Walk.start_mem_support, exists_prop, and_true]
      exact ⟨u, ut⟩
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset] at hv
    obtain ⟨w, wt, hw⟩ := hv
    refine ⟨{x | x ∈ (Gpc u w).some.support}, ?_, ?_⟩
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset]
      exact fun x xw => Set.mem_iUnion₂.mpr ⟨w, wt, xw⟩
    · simp only [Set.mem_setOf_eq, Walk.start_mem_support, exists_true_left]
      refine ⟨hw, Walk.connected_induce_support _ _ _⟩

end induced_subgraphs

end SimpleGraph
