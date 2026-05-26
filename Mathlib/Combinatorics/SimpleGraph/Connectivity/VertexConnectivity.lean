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

This file defines `k`-vertex connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsVertexReachable`: Two vertices are `k`-vertex-reachable if they remain reachable
  after removing strictly fewer than `k` other vertices. Formally, removing a set `s` of
  fewer than `k` vertices amounts to considering the induced subgraph on `sᶜ`.
* `SimpleGraph.IsVertexPreconnected`: A graph is `k`-vertex-preconnected if any two vertices
  are `k`-vertex-reachable, meaning the removal of any set of strictly fewer than `k` vertices
  leaves any pair of vertices outside that set reachable.
* `SimpleGraph.IsVertexConnected`: A graph is `k`-vertex-connected if it is `k`-vertex-preconnected
  and it has more than `k` vertices.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ∞} {u v : V}

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after removing
strictly fewer than `k` other vertices. Formally, after removing `s` (with `s.encard < k`),
reachability is checked in the induced subgraph on the complement `sᶜ`. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → (hu : u ∉ s) → (hv : v ∉ s) →
    (G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩

variable (u) in
@[simp]
lemma IsVertexReachable.refl : G.IsVertexReachable k u u :=
  -- Both endpoints reduce to ⟨u, _⟩; proof irrelevance makes them equal
  fun _ _ _ _ ↦ .rfl

@[symm]
lemma IsVertexReachable.symm (h : G.IsVertexReachable k u v) : G.IsVertexReachable k v u :=
  fun _ hs hv hu ↦ (h hs hu hv).symm

lemma isVertexReachable_comm : G.IsVertexReachable k u v ↔ G.IsVertexReachable k v u :=
  ⟨.symm, .symm⟩

@[gcongr]
lemma IsVertexReachable.mono (hGH : G ≤ H) (h : G.IsVertexReachable k u v) :
    H.IsVertexReachable k u v :=
  -- G.induce sᶜ ≤ H.induce sᶜ because adjacency in the induced subgraph is adjacency in G/H
  fun _ hs hu hv ↦ (h hs hu hv).mono (fun ⟨_, _⟩ ⟨_, _⟩ hadj ↦ hGH hadj)

@[gcongr]
lemma IsVertexReachable.anti (hkl : k ≤ l) (h : G.IsVertexReachable l u v) :
    G.IsVertexReachable k u v :=
  fun _ hs hu hv ↦ h (hs.trans_le hkl) hu hv

@[simp]
lemma IsVertexReachable.zero : G.IsVertexReachable 0 u v :=
  fun _ hs _ _ ↦ absurd hs not_lt_zero

variable (k) in
lemma IsVertexReachable.of_adj (h : G.Adj u v) : G.IsVertexReachable k u v :=
  -- G.Adj u v implies (G.induce sᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ definitionally
  fun _ _ hu hv ↦ Adj.reachable (show (G.induce _).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)

alias Adj.isVertexReachable := IsVertexReachable.of_adj

/-- A vertex pair is reachable if it is `k`-vertex-reachable for `k ≠ 0`. -/
lemma IsVertexReachable.reachable (hk : k ≠ 0) (h : G.IsVertexReachable k u v) :
    G.Reachable u v := by
  -- Instantiate with s = ∅ (removing no vertices)
  have key := h (s := ∅) (by rw [Set.encard_empty]; exact pos_of_ne_zero hk)
    (Set.notMem_empty u) (Set.notMem_empty v)
  -- Embed the walk in G.induce ∅ᶜ back into G
  -- via `Embedding.induce ∅ᶜ : G.induce ∅ᶜ ↪g G`
  exact key.map (Embedding.induce ∅ᶜ).toHom

/-- Reachability under 1-vertex-connectivity is equivalent to standard reachability. -/
@[simp]
lemma isVertexReachable_one_iff : G.IsVertexReachable 1 u v ↔ G.Reachable u v := by
  constructor
  · exact (·.reachable one_ne_zero)
  · intro h s hs hu hv
    -- From hs : s.encard < 1, deduce s = ∅
    have hs0 : s = ∅ := Set.encard_eq_zero.mp (ENat.lt_one_iff_eq_zero.mp hs)
    subst hs0
    -- Now hu : u ∉ ∅, hv : v ∉ ∅;
    -- goal is `(G.induce ∅ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩`
    -- Lift the walk in G to G.induce ∅ᶜ (all vertices lie in ∅ᶜ = Set.univ)
    obtain ⟨w⟩ := h
    exact ⟨w.induce ∅ᶜ fun x _ => Set.notMem_empty x⟩

variable (G k) in
/-- A graph is `k`-vertex-preconnected if any two vertices are `k`-vertex-reachable. -/
def IsVertexPreconnected : Prop :=
  ∀ u v : V, G.IsVertexReachable k u v

@[simp]
lemma IsVertexPreconnected.zero : G.IsVertexPreconnected 0 :=
  fun _ _ ↦ .zero

/-- 1-vertex-preconnectivity is equivalent to preconnectedness. -/
@[simp]
lemma isVertexPreconnected_one : G.IsVertexPreconnected 1 ↔ G.Preconnected := by
  simp [IsVertexPreconnected, isVertexReachable_one_iff, Preconnected]

/-- A preconnected graph is 1-vertex-preconnected. -/
alias ⟨_, Preconnected.isVertexPreconnected_one⟩ := isVertexPreconnected_one

/-- Vertex preconnectivity is antitonic in `k`. -/
@[gcongr]
lemma IsVertexPreconnected.anti (hkl : l ≤ k) (hc : G.IsVertexPreconnected k) :
    G.IsVertexPreconnected l :=
  fun u v ↦ (hc u v).anti hkl

/-- Vertex preconnectivity is monotonic in the graph. -/
@[gcongr]
lemma IsVertexPreconnected.mono (hGH : G ≤ H) (hc : G.IsVertexPreconnected k) :
    H.IsVertexPreconnected k :=
  fun u v ↦ (hc u v).mono hGH

/-- The complete graph on `n` vertices is `k`-vertex-preconnected for any `k`. -/
lemma IsVertexPreconnected.top : (⊤ : SimpleGraph V).IsVertexPreconnected k := by
  intro u v
  by_cases h : u = v
  exacts [h ▸ .refl _, .of_adj _ h]

variable (G k) in
/-- A graph is `k`-vertex-connected if it is `k`-vertex-preconnected and it has more than `k`
vertices. -/
def IsVertexConnected : Prop :=
  k + 1 ≤ ENat.card V ∧ G.IsVertexPreconnected k

/-- A graph is 0-vertex-connected iff it is nonempty. -/
@[simp]
lemma isVertexConnected_zero : G.IsVertexConnected 0 ↔ Nonempty V := by
  simp [IsVertexConnected, ENat.one_le_card_iff_nonempty]

/-- Every nonempty graph is 0-vertex-connected. -/
lemma IsVertexConnected.zero [Nonempty V] : G.IsVertexConnected 0 :=
  isVertexConnected_zero.mpr ‹_›

/-- 1-vertex-connectivity is equivalent to preconnectedness and `V` being nontrivial. -/
@[simp]
lemma isVertexConnected_one : G.IsVertexConnected 1 ↔ Nontrivial V ∧ G.Preconnected := by
  rw [IsVertexConnected, isVertexPreconnected_one, ← ENat.one_lt_card_iff_nontrivial]
  exact and_congr_left' <| ENat.add_one_le_iff ENat.one_ne_top

lemma Preconnected.isVertexConnected_one [Nontrivial V] (h : G.Preconnected) :
    G.IsVertexConnected 1 :=
  SimpleGraph.isVertexConnected_one.mpr ⟨‹_›, h⟩

/-- Vertex connectivity is antitonic in `k`. -/
@[gcongr]
lemma IsVertexConnected.anti (hkl : l ≤ k) (hc : G.IsVertexConnected k) :
    G.IsVertexConnected l := by
  refine ⟨?_, hc.right.anti hkl⟩
  exact le_trans (by gcongr) hc.left

/-- Vertex connectivity is monotonic in the graph. -/
@[gcongr]
lemma IsVertexConnected.mono (hGH : G ≤ H) (hc : G.IsVertexConnected k) : H.IsVertexConnected k :=
  ⟨hc.left, hc.right.mono hGH⟩

/-- The complete graph on `n` vertices is `(n-1)`-vertex-connected. -/
lemma isVertexConnected_top [Nonempty V] :
    (⊤ : SimpleGraph V).IsVertexConnected (ENat.card V - 1) := by
  refine ⟨?_, .top⟩
  simp [← tsub_le_tsub_iff_right <| Order.one_le_iff_pos.mpr ENat.card_pos]

end SimpleGraph
