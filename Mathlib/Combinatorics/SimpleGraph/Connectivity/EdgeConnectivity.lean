/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
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

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Two vertices are `k`-edge-reachable if they remain reachable after removing strictly fewer than
`k` edges. -/
def IsEdgeReachable (k : ℕ) (u v : V) : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v

/-- A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable. -/
def IsEdgeConnected (k : ℕ) : Prop :=
  ∀ u v : V, G.IsEdgeReachable k u v

variable {G} {k : ℕ}

@[simp]
lemma IsEdgeReachable.rfl (u : V) : G.IsEdgeReachable k u u :=
  fun _ _ ↦ .refl _

@[symm]
lemma IsEdgeReachable.symm {u v : V} (h : G.IsEdgeReachable k u v) :
    G.IsEdgeReachable k v u :=
  fun _ hk ↦ (h hk).symm

@[trans]
lemma IsEdgeReachable.trans {u v w : V} (h1 : G.IsEdgeReachable k u v)
    (h2 : G.IsEdgeReachable k v w) : G.IsEdgeReachable k u w :=
  fun _ hk ↦ (h1 hk).trans (h2 hk)

lemma IsEdgeReachable.mono {G' : SimpleGraph V} (hle : G ≤ G') {u v : V}
    (h : G.IsEdgeReachable k u v) : G'.IsEdgeReachable k u v :=
  fun _ hk ↦ h hk |>.mono <| deleteEdges_mono hle

@[gcongr]
lemma IsEdgeReachable.anti {k l : ℕ} (hkl : k ≤ l) {u v : V}
    (h : G.IsEdgeReachable l u v) : G.IsEdgeReachable k u v :=
  fun _ hk ↦ h (lt_of_lt_of_le hk (Nat.cast_le.mpr hkl))

@[simp]
protected lemma IsEdgeReachable.zero {u v : V} : G.IsEdgeReachable 0 u v :=
  fun _ hk ↦ absurd (zero_le _) (not_le_of_gt hk)

@[simp]
protected lemma IsEdgeConnected.zero : G.IsEdgeConnected 0 :=
  fun _ _ ↦ .zero

@[simp]
lemma isEdgeReachable_one {u v : V} : G.IsEdgeReachable 1 u v ↔ G.Reachable u v := by
  refine ⟨fun h ↦ G.deleteEdges_empty ▸ h (by simp), fun h s hs ↦ ?_⟩
  rwa [Set.encard_eq_zero.mp <| ENat.lt_one_iff_eq_zero.mp hs, deleteEdges_empty]

lemma isEdgeConnected_one : G.IsEdgeConnected 1 ↔ G.Preconnected := by
  simp [IsEdgeConnected, Preconnected]

lemma isEdgeReachable_succ {k : ℕ} {u v : V} :
    G.IsEdgeReachable (k + 1) u v ↔
      G.Reachable u v ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).IsEdgeReachable k u v := by
  constructor
  · intro h
    refine ⟨?_, fun e he s hk ↦ ?_⟩
    · specialize (@h ∅) (by simp)
      rwa [deleteEdges_empty] at h
    · rw [deleteEdges_deleteEdges, Set.union_comm]
      apply h
      calc (s ∪ {e}).encard
        _ ≤ s.encard + ({e} : Set (Sym2 V)).encard := Set.encard_union_le _ _
        _ = s.encard + 1 := by rw [Set.encard_singleton]
        _ < k + 1 := (ENat.add_lt_add_iff_right ENat.one_ne_top).mpr hk
  · intro ⟨h_one, h_succ⟩ s hk
    let s' := s ∩ G.edgeSet
    have h_eq : G.deleteEdges s = G.deleteEdges s' := G.deleteEdges_eq_inter_edgeSet s
    rw [h_eq]
    rcases s'.eq_empty_or_nonempty with h_empty | ⟨e, he⟩
    · rw [h_empty, deleteEdges_empty]
      exact h_one
    · have he_edge : e ∈ G.edgeSet := he.2
      have h_ins : insert e (s' \ {e}) = s' := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨hx, -⟩) <;> assumption
        · intro hx
          by_cases h : x = e <;> simp [h, hx]
      nth_rw 1 [← h_ins]
      rw [Set.insert_eq, ← deleteEdges_deleteEdges]
      apply h_succ e he_edge
      have : s'.encard ≤ s.encard := Set.encard_mono Set.inter_subset_left
      have hk' : s'.encard < k + 1 := this.trans_lt hk
      have hsub : s'.encard = (s' \ {e}).encard + 1 :=
        (Set.encard_diff_singleton_add_one (s := s') he).symm
      rw [hsub] at hk'
      exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mp hk'

lemma isEdgeConnected_succ {k : ℕ} :
    G.IsEdgeConnected (k + 1) ↔
      G.IsEdgeConnected 1 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).IsEdgeConnected k := by
  simp only [IsEdgeConnected, isEdgeReachable_succ, IsEdgeReachable.zero]
  exact ⟨fun h ↦ ⟨fun u v ↦ ⟨(h u v).1, fun _ _ ↦ trivial⟩, fun e he u v ↦ (h u v).2 e he⟩,
         fun ⟨h1, h_succ⟩ u v ↦ ⟨(h1 u v).1, fun e he ↦ h_succ e he u v⟩⟩

lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ G.Preconnected ∧ ∀ e, ¬ G.IsBridge e := by
  constructor
  · intro h
    refine ⟨isEdgeConnected_one.mp (fun u v ↦ (h u v).anti (Nat.le_succ 1)), fun e hb ↦ ?_⟩
    induction e using Sym2.ind with | h u v =>
    exact (isBridge_iff.mp hb).2 <| h u v (Set.encard_singleton _ ▸ Nat.one_lt_ofNat)
  · rintro ⟨h_pre, h_bridge⟩ u v
    rw [isEdgeReachable_succ]
    constructor
    · exact h_pre u v
    · intro e he
      rw [isEdgeReachable_one]
      induction e using Sym2.ind with | h x y =>
      have h_conn : G.Connected := { preconnected := h_pre, nonempty := ⟨x⟩ }
      exact (h_conn.connected_delete_edge_of_not_isBridge (h_bridge _)).preconnected u v

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

end SimpleGraph
