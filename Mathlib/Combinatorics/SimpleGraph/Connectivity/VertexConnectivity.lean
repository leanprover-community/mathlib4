/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!
# Vertex Connectivity

This file defines `k`-vertex-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsVertexReachable`: Two vertices are `k`-vertex-reachable if they remain reachable
  after removing strictly fewer than `k` vertices, while keeping these endpoints.
* `SimpleGraph.IsVertexConnected`: A graph is `k`-vertex-connected if any two vertices are
  `k`-vertex-reachable.
* `SimpleGraph.vertexReachability`: The largest `k` (as an `ℕ∞`) such that two fixed vertices are
  `k`-vertex-reachable.
* `SimpleGraph.vertexConnectivity`: The largest `k` (as an `ℕ∞`) such that the graph is
  `k`-vertex-connected.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v : V}

variable (G : SimpleGraph V) (s : Set V) in
/-- `G.isolateVerts s` is the graph where all vertices in `s` are isolated. -/
def isolateVerts : SimpleGraph V where
  Adj u v := u ∉ s ∧ v ∉ s ∧ G.Adj u v
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

@[simp]
lemma isolateVerts_empty : G.isolateVerts ∅ = G := by
  ext; simp [isolateVerts]

@[simp]
lemma isolateVerts_le (s : Set V) : G.isolateVerts s ≤ G := fun _ _ h ↦ h.2.2

@[gcongr]
lemma isolateVerts_mono (hGH : G ≤ H) (s : Set V) : G.isolateVerts s ≤ H.isolateVerts s := by
  intro a b hab
  exact ⟨hab.1, hab.2.1, hGH hab.2.2⟩

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after removing strictly fewer
than `k` vertices, while keeping these endpoints. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s → (G.isolateVerts s).Reachable u v

variable (G k) in
/-- A graph is `k`-vertex-connected if any two vertices are `k`-vertex-reachable. -/
def IsVertexConnected : Prop := ∀ u v, G.IsVertexReachable k u v

variable (G u v) in
/-- The vertex reachability number between two vertices. -/
noncomputable def vertexReachability : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsVertexReachable k u v), (k : ℕ∞)

variable (G) in
/-- The vertex connectivity number of a graph. -/
noncomputable def vertexConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsVertexConnected k), (k : ℕ∞)

@[refl, simp] lemma IsVertexReachable.refl (u : V) : G.IsVertexReachable k u u :=
  fun _ _ _ _ ↦ .rfl

lemma le_vertexReachability (h : G.IsVertexReachable k u v) : (k : ℕ∞) ≤ G.vertexReachability u v :=
  le_iSup_of_le k <| le_iSup_of_le h le_rfl

lemma le_vertexConnectivity (h : G.IsVertexConnected k) : (k : ℕ∞) ≤ G.vertexConnectivity :=
  le_iSup_of_le k <| le_iSup_of_le h le_rfl

lemma vertexConnectivity_le_vertexReachability (u v : V) :
    G.vertexConnectivity ≤ G.vertexReachability u v := by
  refine iSup_le ?_
  intro k
  refine iSup_le ?_
  intro hk
  exact G.le_vertexReachability (u := u) (v := v) (hk u v)

@[symm]
lemma IsVertexReachable.symm (h : G.IsVertexReachable k u v) : G.IsVertexReachable k v u :=
  fun _ hs hv hu ↦ (h hs hu hv).symm

lemma isVertexReachable_comm : G.IsVertexReachable k u v ↔ G.IsVertexReachable k v u :=
  ⟨.symm, .symm⟩

@[gcongr]
lemma IsVertexReachable.mono (hGH : G ≤ H) (h : G.IsVertexReachable k u v) :
    H.IsVertexReachable k u v := by
  intro s hs hu hv
  exact (h hs hu hv).mono <| G.isolateVerts_mono (H := H) hGH s

@[gcongr]
lemma IsVertexReachable.anti (hkl : k ≤ l) (h : G.IsVertexReachable l u v) :
    G.IsVertexReachable k u v :=
  fun _ hs ↦ h <| by grw [← hkl]; exact hs

@[simp]
protected lemma IsVertexReachable.zero : G.IsVertexReachable 0 u v := by
  simp [IsVertexReachable]

@[simp] protected lemma IsVertexConnected.zero : G.IsVertexConnected 0 := fun _ _ ↦ .zero

@[simp]
lemma isVertexReachable_one : G.IsVertexReachable 1 u v ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h (s := ∅) (by simp) (by simp) (by simp)
  · intro h s hs hu hv
    have hs0 : s.encard = 0 := ENat.lt_one_iff_eq_zero.mp hs
    have hs_empty : s = ∅ := Set.encard_eq_zero.mp hs0
    subst hs_empty
    simpa using h

@[simp]
lemma isVertexConnected_one : G.IsVertexConnected 1 ↔ G.Preconnected := by
  simp [IsVertexConnected, Preconnected]

lemma IsVertexReachable.reachable (hk : k ≠ 0) (h : G.IsVertexReachable k u v) : G.Reachable u v :=
  isVertexReachable_one.mp (h.anti (Nat.one_le_iff_ne_zero.mpr hk))

lemma IsVertexConnected.preconnected (hk : k ≠ 0) (h : G.IsVertexConnected k) : G.Preconnected :=
  fun u v ↦ (h u v).reachable hk

lemma IsVertexConnected.connected [Nonempty V] (hk : k ≠ 0) (h : G.IsVertexConnected k) :
    G.Connected where
  preconnected := h.preconnected hk

end SimpleGraph
