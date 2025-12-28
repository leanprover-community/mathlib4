/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

/-!
# Vertex Connectivity

This file defines k-vertex-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsVertexReachable`: Two vertices are `k`-vertex-reachable if they remain reachable
  after removing strictly fewer than `k` other vertices.
* `SimpleGraph.IsVertexConnected`: A graph is `k`-vertex-connected if its order is strictly
  greater than `k` and any two distinct vertices are `k`-vertex-reachable.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v : V}

/-- `G.deleteVerts s` is the graph where all vertices in `s` are isolated. -/
def deleteVerts (G : SimpleGraph V) (s : Set V) : SimpleGraph V where
  Adj u v := u ∉ s ∧ v ∉ s ∧ G.Adj u v
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

@[simp]
lemma deleteVerts_empty : G.deleteVerts ∅ = G := by
  ext; simp [deleteVerts]

@[simp]
lemma deleteVerts_subset_le (s : Set V) : G.deleteVerts s ≤ G :=
  fun _ _ h ↦ h.2.2

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after removing
strictly fewer than `k` other vertices. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s → (G.deleteVerts s).Reachable u v

@[simp]
lemma IsVertexReachable.refl (u : V) : G.IsVertexReachable k u u :=
  fun _ _ _ _ ↦ .refl _

@[symm]
lemma IsVertexReachable.symm (h : G.IsVertexReachable k u v) : G.IsVertexReachable k v u :=
  fun _ hs hv hu ↦ (h hs hu hv).symm

@[gcongr]
lemma IsVertexReachable.mono (hGH : G ≤ H) (h : G.IsVertexReachable k u v) :
    H.IsVertexReachable k u v :=
  fun _ hs hu hv ↦ (h hs hu hv).mono (by intro _ _ ⟨h1, h2, h3⟩; exact ⟨h1, h2, hGH h3⟩)

@[gcongr]
lemma IsVertexReachable.anti (hkl : k ≤ l) (h : G.IsVertexReachable l u v) :
    G.IsVertexReachable k u v :=
  fun _ hs ↦ h (hs.trans_le hkl)

@[simp]
protected lemma IsVertexReachable.zero : G.IsVertexReachable 0 u v :=
  fun _ hs ↦ absurd hs (not_lt_of_ge (zero_le _))

lemma IsVertexReachable.of_adj (h : G.Adj u v) (k : ℕ∞) : G.IsVertexReachable k u v :=
  fun _ _ hu hv ↦ (Adj.reachable ⟨hu, hv, h⟩)

/-- A vertex pair is reachable if it is `k`-vertex-reachable for `k ≠ 0`. -/
lemma IsVertexReachable.reachable {hk : k ≠ 0} (h : G.IsVertexReachable k u v) :
    G.Reachable u v := by
  have := pos_iff_ne_zero.mpr hk
  specialize h (s := ∅) (by simpa) (by simp) (by simp)
  rwa [deleteVerts_empty] at h

variable (G k) in
/-- A graph is `k`-vertex-connected if its order is strictly greater than `k`
and any two distinct vertices are `k`-vertex-reachable. -/
def IsVertexConnected [Fintype V] (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ u v : V, u ≠ v → G.IsVertexReachable k u v

@[simp]
protected lemma IsVertexConnected.zero [Fintype V] : G.IsVertexConnected 0 ↔ Nonempty V := by
  simp [IsVertexConnected, Fintype.card_pos_iff]

/-- 1-vertex-connectivity is equivalent to being a connected graph with at least 2 vertices. -/
@[simp]
protected lemma IsVertexConnected.one [Fintype V] :
    G.IsVertexConnected 1 ↔ 1 < Fintype.card V ∧ G.Connected := by
  classical
  constructor
  · rintro ⟨h_card, h_reach⟩
    refine ⟨h_card, ?_⟩
    rw [connected_iff_exists_forall_reachable]
    have := Fintype.card_pos_iff.1 (zero_lt_one.trans h_card)
    rcases this with ⟨x⟩
    refine ⟨x, fun y ↦ ?_⟩
    by_cases hxy : x = y
    · subst hxy; exact .refl _
    · specialize h_reach x y hxy
      simpa using h_reach (s := ∅) (by simp)
  · rintro ⟨h_card, h_conn⟩
    refine ⟨h_card, fun u v huv ↦ ?_⟩
    intro s hs hu hv
    have : s = ∅ := by
      rw [← Set.encard_eq_zero, ← ENat.lt_one_iff_eq_zero]
      exact_mod_cast hs
    subst this
    rw [deleteVerts_empty]
    exact h_conn.preconnected u v

/-- Vertex connectivity is monotonic in `k`. -/
@[gcongr]
lemma IsVertexConnected.anti [Fintype V] {k l : ℕ} (hkl : l ≤ k) (hc : G.IsVertexConnected k) :
    G.IsVertexConnected l :=
  ⟨lt_of_le_of_lt hkl hc.1,
   fun u v huv ↦ IsVertexReachable.anti (Nat.cast_le.mpr hkl) (hc.2 u v huv)⟩

/-- Vertex connectivity is monotonic in the graph. -/
@[gcongr]
lemma IsVertexConnected.mono [Fintype V] {k : ℕ} (hGH : G ≤ H) (hc : G.IsVertexConnected k) :
    H.IsVertexConnected k :=
  ⟨hc.1, fun u v huv ↦ IsVertexReachable.mono hGH (hc.2 u v huv)⟩

/-- The complete graph on `n` vertices is `(n-1)`-vertex-connected. -/
lemma completeGraph_isVertexConnected [Fintype V] (h : 1 < Fintype.card V) :
    (⊤ : SimpleGraph V).IsVertexConnected (Fintype.card V - 1) :=
  ⟨Nat.sub_lt (lt_trans Nat.zero_lt_one h) Nat.zero_lt_one,
   fun u v huv ↦ IsVertexReachable.of_adj (by simp [huv]) _⟩

end SimpleGraph
