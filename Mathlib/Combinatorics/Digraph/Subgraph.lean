/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shashank Kirtania
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Set.Basic

/-!
# Subgraphs of Directed Graphs

This file defines subgraphs of directed graphs and their properties.

## Main definitions

* `Digraph.Subgraph` - A subgraph of a directed graph
* `Digraph.Subgraph.IsInduced` - Predicate for induced subgraphs
* `Digraph.Subgraph.induced` - The induced subgraph on a set of vertices

-/

namespace Digraph

universe u v

variable {V : Type u} (G : Digraph V)

/-- A subgraph of a directed graph -/
@[ext]
structure Subgraph where
  /-- The vertex set of the subgraph -/
  verts : Set V
  /-- The adjacency relation of the subgraph -/
  Adj : V → V → Prop
  /-- Edges must have their source in the vertex set -/
  edge_vert_fst : ∀ {v w}, Adj v w → v ∈ verts
  /-- Edges must have their target in the vertex set -/
  edge_vert_snd : ∀ {v w}, Adj v w → w ∈ verts
  /-- The subgraph's edges are a subset of the parent graph's edges -/
  adj_sub : ∀ {v w}, Adj v w → G.Adj v w

namespace Subgraph

variable {G : Digraph V}

protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert_fst h

protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  H.edge_vert_snd h

protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h

/-- A subgraph is induced if it contains all edges between its vertices -/
structure IsInduced (G' : G.Subgraph) : Prop where
  induced : ∀ {v w}, v ∈ G'.verts → w ∈ G'.verts → G.Adj v w → G'.Adj v w

/-- The induced subgraph on a set of vertices -/
def induced (s : Set V) : G.Subgraph where
  verts := s
  Adj v w := v ∈ s ∧ w ∈ s ∧ G.Adj v w
  edge_vert_fst := fun h => h.1
  edge_vert_snd := fun h => h.2.1
  adj_sub := fun h => h.2.2

@[simp]
theorem verts_induced (s : Set V) : (@induced _ G s).verts = s := rfl

@[simp]
theorem Adj_induced (s : Set V) {v w : V} :
    (@induced _ G s).Adj v w ↔ v ∈ s ∧ w ∈ s ∧ G.Adj v w := Iff.rfl

theorem induced_adj_of_mem {s : Set V} {v w : V} (hv : v ∈ s) (hw : w ∈ s) :
    (@induced _ G s).Adj v w ↔ G.Adj v w := by
  simp only [Adj_induced, hv, hw, true_and]

/-- A subgraph is induced iff it equals the induced subgraph on its vertices -/
theorem isInduced_iff_eq_induced (G' : G.Subgraph) :
    IsInduced G' ↔ G' = induced G'.verts := by
  constructor
  · intro h
    ext v w
    · simp
    · simp only [Adj_induced]
      constructor
      · intro h'
        exact ⟨G'.edge_vert_fst h', G'.edge_vert_snd h', G'.adj_sub h'⟩
      · intro ⟨hv, hw, hvw⟩
        exact h.induced hv hw hvw
  · intro h
    constructor
    intro v w hv hw hvw
    rw [h]
    simp only [Adj_induced, hv, hw, hvw, and_self]

/-- The `top` subgraph is `G` as a subgraph of itself -/
instance : Top G.Subgraph where
  top :=
    { verts := Set.univ
      Adj := G.Adj
      edge_vert_fst := fun _ => Set.mem_univ _
      edge_vert_snd := fun _ => Set.mem_univ _
      adj_sub := fun h => h }

/-- The `bot` subgraph has no vertices or edges -/
instance : Bot G.Subgraph where
  bot :=
    { verts := ∅
      Adj := ⊥
      edge_vert_fst := fun h => h.elim
      edge_vert_snd := fun h => h.elim
      adj_sub := fun h => h.elim }

theorem top_verts : (⊤ : G.Subgraph).verts = Set.univ := rfl

theorem top_Adj {v w : V} : (⊤ : G.Subgraph).Adj v w ↔ G.Adj v w := Iff.rfl

theorem bot_verts : (⊥ : G.Subgraph).verts = ∅ := rfl

theorem not_bot_Adj {v w : V} : ¬ (⊥ : G.Subgraph).Adj v w := not_false

/-- Subgraph order: G₁ ≤ G₂ if vertices and edges are subsets -/
instance : LE G.Subgraph where
  le G₁ G₂ := G₁.verts ⊆ G₂.verts ∧ ∀ v w, G₁.Adj v w → G₂.Adj v w

theorem le_def {G₁ G₂ : G.Subgraph} :
    G₁ ≤ G₂ ↔ G₁.verts ⊆ G₂.verts ∧ ∀ v w, G₁.Adj v w → G₂.Adj v w := Iff.rfl

/-- The union of two subgraphs -/
instance : Max G.Subgraph where
  max G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      edge_vert_fst := fun h =>
        h.elim (fun h' => Or.inl (G₁.edge_vert_fst h')) (fun h' => Or.inr (G₂.edge_vert_fst h'))
      edge_vert_snd := fun h =>
        h.elim (fun h' => Or.inl (G₁.edge_vert_snd h')) (fun h' => Or.inr (G₂.edge_vert_snd h'))
      adj_sub := fun h => h.elim G₁.adj_sub G₂.adj_sub }

/-- The intersection of two subgraphs -/
instance : Min G.Subgraph where
  min G₁ G₂ :=
    { verts := G₁.verts ∩ G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      edge_vert_fst := fun h => ⟨G₁.edge_vert_fst h.1, G₂.edge_vert_fst h.2⟩
      edge_vert_snd := fun h => ⟨G₁.edge_vert_snd h.1, G₂.edge_vert_snd h.2⟩
      adj_sub := fun h => G₁.adj_sub h.1 }

theorem inf_verts (G₁ G₂ : G.Subgraph) :
    (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts := rfl

theorem inf_Adj (G₁ G₂ : G.Subgraph) {v w : V} :
    (G₁ ⊓ G₂).Adj v w ↔ G₁.Adj v w ∧ G₂.Adj v w := Iff.rfl

theorem sup_verts (G₁ G₂ : G.Subgraph) :
    (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts := rfl

theorem sup_Adj (G₁ G₂ : G.Subgraph) {v w : V} :
    (G₁ ⊔ G₂).Adj v w ↔ G₁.Adj v w ∨ G₂.Adj v w := Iff.rfl

/-- Partial order on subgraphs -/
instance : PartialOrder G.Subgraph where
  le := (· ≤ ·)
  le_refl G' := ⟨Set.Subset.refl _, fun _ _ h => h⟩
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ :=
    ⟨Set.Subset.trans h₁₂.1 h₂₃.1, fun v w h => h₂₃.2 v w (h₁₂.2 v w h)⟩
  le_antisymm G₁ G₂ h₁₂ h₂₁ := by
    ext v w
    · exact ⟨fun hv => h₁₂.1 hv, fun hv => h₂₁.1 hv⟩
    · exact ⟨h₁₂.2 v w, h₂₁.2 v w⟩

/-- Lattice structure on subgraphs -/
instance : Lattice G.Subgraph where
  sup := (· ⊔ ·)
  le_sup_left G₁ G₂ :=
    ⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩
  le_sup_right G₁ G₂ :=
    ⟨Set.subset_union_right, fun _ _ h => Or.inr h⟩
  sup_le G₁ G₂ G₃ h₁ h₂ :=
    ⟨Set.union_subset h₁.1 h₂.1, fun v w h => h.elim (h₁.2 v w) (h₂.2 v w)⟩
  inf := (· ⊓ ·)
  inf_le_left G₁ G₂ :=
    ⟨Set.inter_subset_left, fun _ _ h => h.1⟩
  inf_le_right G₁ G₂ :=
    ⟨Set.inter_subset_right, fun _ _ h => h.2⟩
  le_inf G₁ G₂ G₃ h₁ h₂ :=
    ⟨Set.subset_inter h₁.1 h₂.1, fun v w h => ⟨h₁.2 v w h, h₂.2 v w h⟩⟩

theorem bot_le (G' : G.Subgraph) : ⊥ ≤ G' :=
  ⟨Set.empty_subset _, fun _ _ h => h.elim⟩

theorem le_top (G' : G.Subgraph) : G' ≤ ⊤ :=
  ⟨Set.subset_univ _, fun _ _ h => G'.adj_sub h⟩

instance : BoundedOrder G.Subgraph where
  top := ⊤
  le_top := le_top
  bot := ⊥
  bot_le := bot_le

theorem IsInduced.top : (⊤ : G.Subgraph).IsInduced :=
  ⟨fun _ _ h => h⟩

end Subgraph

end Digraph
