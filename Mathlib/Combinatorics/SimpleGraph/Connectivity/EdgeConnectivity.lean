/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v w : V}

variable (G k u v) in
/-- Two vertices are `k`-edge-reachable if they remain reachable after removing strictly fewer than
`k` edges. -/
def IsEdgeReachable : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v

variable (G k) in
/-- A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable. -/
def IsEdgeConnected : Prop := ∀ u v, G.IsEdgeReachable k u v

@[refl, simp] lemma IsEdgeReachable.refl (u : V) : G.IsEdgeReachable k u u := fun _ _ ↦ .rfl

@[deprecated (since := "2026-01-06")] alias IsEdgeReachable.rfl := IsEdgeReachable.refl

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

lemma isEdgeReachable_add_one :
    G.IsEdgeReachable (k + 1) u v ↔
      G.Reachable u v ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).IsEdgeReachable k u v := by
  refine ⟨fun h ↦ ⟨G.deleteEdges_empty ▸ h (by simp), fun e he s hk ↦ ?_⟩, ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
    exact ENat.add_lt_add_iff_right ENat.one_ne_top |>.mpr hk
  · intro ⟨h_one, h_succ⟩ s hk
    rw [G.deleteEdges_eq_inter_edgeSet s]
    rcases (s ∩ G.edgeSet).eq_empty_or_nonempty with h_empty | ⟨e, he⟩
    · simpa [h_empty]
    · rw [← Set.insert_diff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
      refine h_succ e he.right <| ENat.add_lt_add_iff_right ENat.one_ne_top |>.mp ?_
      rw [Set.encard_diff_singleton_add_one he]
      exact Set.encard_mono Set.inter_subset_left |>.trans_lt hk

lemma isEdgeConnected_add_one (hk : k ≠ 0) :
    G.IsEdgeConnected (k + 1) ↔ ∀ e, (G.deleteEdges {e}).IsEdgeConnected k := by
  refine ⟨fun h e u v ↦ ?_, fun h u v ↦ isEdgeReachable_add_one.mpr ⟨?_, fun e _ ↦ h e u v⟩⟩
  · by_cases he : e ∈ G.edgeSet
    · exact (isEdgeReachable_add_one.mp <| h u v).right e he
    · rw [G.deleteEdges_eq_self.mpr <| Set.disjoint_singleton_right.mpr he]
      exact h u v |>.anti <| k.le_succ
  · refine isEdgeReachable_one.mp ?_ |>.mono <| G.deleteEdges_le {s(u, v)}
    exact h _ u v |>.anti <| k.one_le_iff_ne_zero.mpr hk

/-- A graph is 2-edge-connected iff it is preconnected and has no bridges. -/
lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ G.Preconnected ∧ ∀ e, ¬G.IsBridge e := by
  refine ⟨fun h ↦ ⟨fun u v ↦ isEdgeReachable_one.mp <| .anti (Nat.le_succ 1) (h u v), ?_⟩, ?_⟩
  · rintro ⟨⟩ he_bridge
    exact he_bridge.right <| h _ _ <| Set.encard_singleton _ ▸ Nat.one_lt_ofNat
  · refine fun ⟨h_pre, h_bridge⟩ u v ↦ isEdgeReachable_add_one.mpr ⟨h_pre u v, ?_⟩
    · rintro ⟨⟩ he
      apply isEdgeReachable_one.mpr
      have h_conn : G.Connected := { preconnected := h_pre, nonempty := ⟨‹_›⟩ }
      exact (h_conn.connected_delete_edge_of_not_isBridge <| h_bridge _).preconnected ..

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

lemma IsEdgeReachable.reachable (hk : k ≠ 0) (huv : G.IsEdgeReachable k u v) : G.Reachable u v :=
  isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

lemma IsEdgeConnected.preconnected (hk : k ≠ 0) (h : G.IsEdgeConnected k) : G.Preconnected :=
  fun u v ↦ (h u v).reachable hk

lemma IsEdgeConnected.connected [Nonempty V] (hk : k ≠ 0) (h : G.IsEdgeConnected k) :
    G.Connected where
  preconnected := h.preconnected hk

end SimpleGraph
