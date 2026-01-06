/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.IsolateVerts
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

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after removing
strictly fewer than `k` other vertices. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s → (G.isolateVerts s).Reachable u v

variable (u) in
@[simp]
lemma IsVertexReachable.refl : G.IsVertexReachable k u u :=
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

variable (k) in
lemma IsVertexReachable.of_adj (h : G.Adj u v) : G.IsVertexReachable k u v :=
  fun _ _ hu hv ↦ Adj.reachable ⟨hu, hv, h⟩

alias Adj.isVertexReachable := IsVertexReachable.of_adj

/-- A vertex pair is reachable if it is `k`-vertex-reachable for `k ≠ 0`. -/
lemma IsVertexReachable.reachable (hk : k ≠ 0) (h : G.IsVertexReachable k u v) :
    G.Reachable u v := by
  rw [← G.isolateVerts_empty]
  apply h <;> simp [pos_of_ne_zero hk]

variable (G k) in
/-- A graph is `k`-vertex-connected if it has more than `k` vertices
and any two vertices are `k`-vertex-reachable. -/
def IsVertexConnected : Prop :=
  k + 1 ≤ ENat.card V ∧ ∀ u v : V, G.IsVertexReachable k u v

@[simp]
lemma isVertexConnected_zero : G.IsVertexConnected 0 ↔ Nonempty V := by
  simp [IsVertexConnected, ENat.one_le_card_iff_nonempty]

/-- A nonempty graph is 0-vertex-connected. -/
lemma IsVertexConnected.zero [Nonempty V] : G.IsVertexConnected 0 :=
  isVertexConnected_zero.mpr ‹_›

/-- Reachability under 1-vertex-connectivity is equivalent to standard reachability. -/
lemma isVertexReachable_one_iff :
    G.IsVertexReachable 1 u v ↔ G.Reachable u v := by
  constructor
  · exact fun h ↦ h.reachable (by simp)
  · rintro h s hs hu hv
    rw [ENat.lt_one_iff_eq_zero, Set.encard_eq_zero] at hs
    rw [hs, isolateVerts_empty]
    exact h

/-- 1-vertex-connectivity is equivalent to being a connected graph with at least 2 vertices. -/
@[simp]
lemma isVertexConnected_one :
    G.IsVertexConnected 1 ↔ Nontrivial V ∧ G.Connected := by
  rw [IsVertexConnected, ENat.add_one_le_iff (by simp), ENat.one_lt_card_iff_nontrivial]
  constructor
  · rintro ⟨h_nt, h_reach⟩
    refine ⟨h_nt, ?_⟩
    haveI : Nontrivial V := h_nt
    exact {
      nonempty := inferInstance
      preconnected := fun u v ↦ (h_reach u v).reachable (by simp)
    }
  · rintro ⟨h_nt, h_conn⟩
    exact ⟨h_nt, fun u v ↦ isVertexReachable_one_iff.mpr (h_conn.preconnected u v)⟩

/-- Vertex connectivity is antitonic in `k`. -/
@[gcongr]
lemma IsVertexConnected.anti (hkl : l ≤ k) (hc : G.IsVertexConnected k) :
    G.IsVertexConnected l :=
  ⟨by exact (add_le_add hkl le_rfl).trans hc.1, fun u v ↦ (hc.2 u v).anti hkl⟩

/-- Vertex connectivity is monotonic in the graph. -/
@[gcongr]
lemma IsVertexConnected.mono (hGH : G ≤ H) (hc : G.IsVertexConnected k) :
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
    · exact IsVertexReachable.of_adj _ h

end SimpleGraph
