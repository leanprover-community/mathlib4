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

This file defines k-vertex connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsVertexReachable`: Two vertices are `k`-vertex-reachable if they remain reachable
  after removing strictly fewer than `k` other vertices.
* `SimpleGraph.IsVertexConnected`: A graph is `k`-vertex-connected if it has more than `k`
  vertices and any two vertices are `k`-vertex-reachable.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v : V}

/-- `G.isolateVerts s` is the graph where all vertices in `s` are isolated. -/
def isolateVerts (G : SimpleGraph V) (s : Set V) : SimpleGraph V where
  Adj u v := u ∉ s ∧ v ∉ s ∧ G.Adj u v
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

@[simp]
lemma isolateVerts_empty : G.isolateVerts ∅ = G := by
  ext; simp [isolateVerts]

@[simp]
lemma isolateVerts_bot (s : Set V) : (⊥ : SimpleGraph V).isolateVerts s = ⊥ := by
  ext; simp [isolateVerts]

@[simp]
lemma isolateVerts_le (s : Set V) : G.isolateVerts s ≤ G :=
  fun _ _ h ↦ h.2.2

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after removing
strictly fewer than `k` other vertices. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s → (G.isolateVerts s).Reachable u v

@[simp]
lemma IsVertexReachable.refl (u : V) : G.IsVertexReachable k u u :=
  fun _ _ _ _ ↦ .refl _

@[symm]
lemma IsVertexReachable.symm (h : G.IsVertexReachable k u v) : G.IsVertexReachable k v u :=
  fun _ hs hv hu ↦ (h hs hu hv).symm

lemma isVertexReachable_symm : G.IsVertexReachable k u v ↔ G.IsVertexReachable k v u :=
  ⟨.symm, .symm⟩

@[gcongr]
lemma IsVertexReachable.mono (hGH : G ≤ H) (h : G.IsVertexReachable k u v) :
    H.IsVertexReachable k u v :=
  fun _ hs hu hv ↦ (h hs hu hv).mono (by intro _ _ ⟨h1, h2, h3⟩; exact ⟨h1, h2, hGH h3⟩)

@[gcongr]
lemma IsVertexReachable.anti (hkl : k ≤ l) (h : G.IsVertexReachable l u v) :
    G.IsVertexReachable k u v :=
  fun _ hs ↦ h (hs.trans_le hkl)

@[simp]
lemma IsVertexReachable.zero : G.IsVertexReachable 0 u v :=
  fun _ hs ↦ absurd hs not_lt_zero

lemma IsVertexReachable.of_adj (h : G.Adj u v) (k : ℕ∞) : G.IsVertexReachable k u v :=
  fun _ _ hu hv ↦ (Adj.reachable ⟨hu, hv, h⟩)

alias _root_.SimpleGraph.Adj.isVertexReachable := IsVertexReachable.of_adj

/-- A vertex pair is reachable if it is `k`-vertex-reachable for `k ≠ 0`. -/
lemma IsVertexReachable.reachable (hk : k ≠ 0) (h : G.IsVertexReachable k u v) :
    G.Reachable u v := by
  rw [← G.isolateVerts_empty]
  apply h <;> simp [pos_of_ne_zero hk]

variable (G) (k : ℕ∞) in
/-- A graph is `k`-vertex-connected if it has more than `k` vertices
and any two vertices are `k`-vertex-reachable. -/
def IsVertexConnected : Prop :=
  k + 1 ≤ ENat.card V ∧ ∀ u v : V, G.IsVertexReachable k u v

@[simp]
lemma isVertexConnected_zero : G.IsVertexConnected 0 ↔ Nonempty V := by
  rw [IsVertexConnected]
  have h0 : (0 : ℕ∞) + 1 = 1 := rfl
  rw [h0]
  simp [ENat.one_le_card_iff_nonempty]

/-- 1-vertex-connectivity is equivalent to being a connected graph with at least 2 vertices. -/
lemma isVertexConnected_one :
    G.IsVertexConnected 1 ↔ 2 ≤ ENat.card V ∧ G.Connected := by
  rw [IsVertexConnected]
  have h1 : (1 : ℕ∞) + 1 = 2 := rfl
  rw [h1]
  constructor
  · rintro ⟨h_card, h_reach⟩
    refine ⟨h_card, ?_⟩
    rw [connected_iff_exists_forall_reachable]
    have h_ne : Nonempty V := by
      rw [← ENat.one_le_card_iff_nonempty]
      exact (self_le_add_right (1 : ℕ∞) 1).trans h_card
    rcases h_ne with ⟨x⟩
    refine ⟨x, fun y ↦ (h_reach x y).reachable (by simp)⟩
  · rintro ⟨h_card, h_conn⟩
    refine ⟨h_card, fun u v s hs _ _ ↦ ?_⟩
    have : s = ∅ := by
      rw [← Set.encard_eq_zero, ← ENat.lt_one_iff_eq_zero]
      exact hs
    subst this
    rw [isolateVerts_empty]
    exact h_conn.preconnected u v

/-- Vertex connectivity is antitonic in `k`. -/
lemma IsVertexConnected.anti {k l : ℕ∞} (hkl : l ≤ k) (hc : G.IsVertexConnected k) :
    G.IsVertexConnected l := by
  constructor
  · let h_le := add_le_add_right hkl 1
    let h_card := hc.1
    have h1 : l + 1 = 1 + l := add_comm ..
    have h2 : k + 1 = 1 + k := add_comm ..
    rw [h1]
    rw [h2] at h_card
    exact h_le.trans h_card
  · exact fun u v ↦ (hc.2 u v).anti hkl

/-- Vertex connectivity is monotonic in the graph. -/
lemma IsVertexConnected.mono {k : ℕ∞} (hGH : G ≤ H) (hc : G.IsVertexConnected k) :
    H.IsVertexConnected k :=
  ⟨hc.1, fun u v ↦ (hc.2 u v).mono hGH⟩

/-- The complete graph on `n` vertices is `(n-1)`-vertex-connected. -/
lemma isVertexConnected_top [Fintype V] [Nonempty V] :
    (⊤ : SimpleGraph V).IsVertexConnected (Fintype.card V - 1) := by
  constructor
  · rw [ENat.card_eq_coe_fintype_card]
    norm_cast
    exact Nat.sub_add_cancel Fintype.card_pos |>.le
  · intro u v
    by_cases h : u = v
    · subst h; exact .refl _
    · exact IsVertexReachable.of_adj h _

end SimpleGraph
