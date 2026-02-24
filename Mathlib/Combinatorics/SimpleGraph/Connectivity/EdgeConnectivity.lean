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

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v w x : V}

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

lemma IsEdgeReachable.reachable (hk : k ≠ 0) (huv : G.IsEdgeReachable k u v) : G.Reachable u v :=
  isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

lemma IsEdgeConnected.preconnected (hk : k ≠ 0) (h : G.IsEdgeConnected k) : G.Preconnected :=
  fun u v ↦ (h u v).reachable hk

lemma IsEdgeConnected.connected [Nonempty V] (hk : k ≠ 0) (h : G.IsEdgeConnected k) :
    G.Connected where
  preconnected := h.preconnected hk

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
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_swap (α := Sym2 _)]

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

lemma isEdgeReachable_two : G.IsEdgeReachable 2 u v ↔ ∀ e, (G.deleteEdges {e}).Reachable u v := by
  simp [isEdgeReachable_add_one]

/-- A graph is 2-edge-connected iff it has no bridge. -/
-- TODO: This should be `G.IsEdgeConnected 2 ↔ ∀ e, ¬G.IsBridge e` after
-- https://github.com/leanprover-community/mathlib4/pull/32583
lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ ∀ e, (G.deleteEdges {e}).Preconnected := by
  simp [isEdgeConnected_add_one]

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {w : G.Walk u v}

/-- A trail doesn't go through a vertex that is not 2-edge-reachable from its 2-edge-reachable
endpoints. -/
lemma IsTrail.not_mem_edges_of_not_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : ¬ G.IsEdgeReachable 2 u x) : x ∉ w.support := by
  classical
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy ↦
    he <| (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy ↦ hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')

end SimpleGraph.Walk
