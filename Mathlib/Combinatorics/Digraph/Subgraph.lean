/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Combinatorics.Digraph.Basic

/-!
# Subgraphs of a digraph

This file defines subgraphs of a digraph. A subgraph consists of a subset of vertices and a subset of
the adjacency relation of the original digraph, such that the endpoints of each edge in the subgraph
are present in the vertex subset.

## Main definitions

* `Digraph.Subgraph G` is the type of subgraphs of a `G : Digraph V`.

* `Digraph.Subgraph.coe` is the coercion from a `G' : Digraph.Subgraph G` to a `Digraph G'.verts`.

* `Digraph.Subgraph.IsSpanning` for whether a subgraph is a spanning subgraph and
  `Digraph.Subgraph.IsInduced` for whether a subgraph is an induced subgraph.

* Instances for `Lattice (Digraph.Subgraph G)` and `BoundedOrder (Digraph.Subgraph G)`.

## Implementation notes

* Subgraphs maintain the directed nature of the original graph, preserving the adjacency relation's directionality.
-/

namespace Digraph

universe u v

variable {V : Type u} {W : Type v}

/-- A subgraph of a `Digraph` is a subset of vertices along with a restriction of the adjacency
relation that is supported by the vertex subset. They also form a bounded lattice.

The adjacency relation `Adj` of a subgraph must be a subset of the adjacency relation of the original graph. -/
@[ext]
structure Subgraph {V : Type u} (G : Digraph V) where
  /-- Vertices of the subgraph -/
  verts : Set V
  /-- Edges of the subgraph -/
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, Adj v w → G.Adj v w
  edge_vert_fst : ∀ {v w : V}, Adj v w → v ∈ verts
  edge_vert_snd : ∀ {v w : V}, Adj v w → w ∈ verts

namespace Subgraph

variable {G : Digraph V} {G₁ G₂ : G.Subgraph} {a b : V}

/-- The one-vertex subgraph. -/
@[simps]
protected def singleton (G : Digraph V) (v : V) : G.Subgraph where
  verts := {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert_fst := False.elim
  edge_vert_snd := False.elim

/-- Coercion from `G' : Subgraph G` to a `Digraph G'.verts`. -/
@[simps]
protected def coe (G' : Subgraph G) : Digraph G'.verts where
  Adj v w := G'.Adj v w

@[simp]
theorem Adj.adj_sub' (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v) : G.Adj u v :=
  G'.adj_sub h

theorem coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert_fst h

protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  H.edge_vert_snd h

/-- Given a digraph `G` and a predicate on vertices `p`, construct the subgraph consisting of
vertices satisfying `p` and all edges between them from `G`. -/
@[simps]
def induced (G : Digraph V) (p : V → Prop) : G.Subgraph where
  verts := {v | p v}
  Adj v w := G.Adj v w ∧ p v ∧ p w
  adj_sub := fun ⟨h, _, _⟩ ↦ h
  edge_vert_fst := fun ⟨_, hp, _⟩ ↦ hp
  edge_vert_snd := fun ⟨_, _, hp⟩ ↦ hp

/-- A subgraph is induced if its adjacency relation includes all edges of the original graph
between vertices of the subgraph. -/
@[mk_iff]
class IsInduced (G' : Subgraph G) : Prop where
  /-- Every edge in the original graph between vertices in the subgraph is also in the subgraph -/
  induced : ∀ {v w}, v ∈ G'.verts → w ∈ G'.verts → G.Adj v w → G'.Adj v w

theorem isInduced_iff_subset_induced (G' : G.Subgraph) :
    IsInduced G' ↔ G' = G.induced fun v ↦ v ∈ G'.verts := by
  constructor
  · intro h
    ext v w
    · simp
    · simp [induced_Adj]
      constructor
      · intro h'
        exact ⟨G'.adj_sub h', G'.edge_vert_fst h', G'.edge_vert_snd h'⟩
      · rintro ⟨h', hv, hw⟩
        exact IsInduced.induced hv hw h'
  · intro h
    constructor
    intro v w hv hw hvw
    rw [h]
    simp [induced_Adj, hv, hw, hvw]

/-- A subgraph is spanning if it contains all vertices of the original graph. -/
class IsSpanning (G' : Subgraph G) : Prop where
  /-- All vertices in the original graph are in the subgraph -/
  verts_eq : G'.verts = Set.univ

theorem isSpanning_iff_verts_eq_univ (G' : G.Subgraph) : IsSpanning G' ↔ G'.verts = Set.univ :=
  ⟨fun h ↦ h.verts_eq, fun h ↦ ⟨h⟩⟩

/-- The empty subgraph, containing no vertices and no edges. -/
@[simps]
def bot (G : Digraph V) : G.Subgraph where
  verts := ∅
  Adj := ⊥
  adj_sub := False.elim
  edge_vert_fst := False.elim
  edge_vert_snd := False.elim

instance (G : Digraph V) : Bot (G.Subgraph) where
  bot := G.Subgraph.bot

/-- The full subgraph, containing all vertices and edges of the original digraph. -/
@[simps]
def top (G : Digraph V) : G.Subgraph where
  verts := Set.univ
  Adj := G.Adj
  adj_sub := id
  edge_vert_fst := fun _ ↦ Set.mem_univ _
  edge_vert_snd := fun _ ↦ Set.mem_univ _

instance (G : Digraph V) : Top (G.Subgraph) where
  top := G.Subgraph.top

instance isSpanning_top (G : Digraph V) : IsSpanning (⊤ : G.Subgraph) :=
  ⟨rfl⟩

instance isInduced_top (G : Digraph V) : IsInduced (⊤ : G.Subgraph) := by
  constructor
  intro v w _ _ h
  exact h

/-- The meet (infimum) of two subgraphs. -/
@[simps]
def inf (G₁ G₂ : G.Subgraph) : G.Subgraph where
  verts := G₁.verts ∩ G₂.verts
  Adj v w := G₁.Adj v w ∧ G₂.Adj v w
  adj_sub := fun ⟨h, _⟩ ↦ G₁.adj_sub h
  edge_vert_fst := fun ⟨h, _⟩ ↦ ⟨G₁.edge_vert_fst h, G₂.edge_vert_fst h⟩
  edge_vert_snd := fun ⟨h, _⟩ ↦ ⟨G₁.edge_vert_snd h, G₂.edge_vert_snd h⟩

instance (G : Digraph V) : Inf (G.Subgraph) where
  inf := Subgraph.inf

/-- The join (supremum) of two subgraphs. -/
@[simps]
def sup (G₁ G₂ : G.Subgraph) : G.Subgraph where
  verts := G₁.verts ∪ G₂.verts
  Adj v w := G₁.Adj v w ∨ G₂.Adj v w
  adj_sub := fun h ↦ h.elim G₁.adj_sub G₂.adj_sub
  edge_vert_fst := fun h ↦ h.elim (Set.mem_union_left _ ∘ G₁.edge_vert_fst) (Set.mem_union_right _ ∘ G₂.edge_vert_fst)
  edge_vert_snd := fun h ↦ h.elim (Set.mem_union_left _ ∘ G₁.edge_vert_snd) (Set.mem_union_right _ ∘ G₂.edge_vert_snd)

instance (G : Digraph V) : Sup (G.Subgraph) where
  sup := Subgraph.sup

/-- A subgraph is contained in another if its vertices and edges are subsets of the other's. -/
@[simp]
theorem le_def : G₁ ≤ G₂ ↔ G₁.verts ⊆ G₂.verts ∧ ∀ v w, G₁.Adj v w → G₂.Adj v w := by
  constructor <;> intro h
  · rw [← sup_eq_right] at h
    have verts_eq := congr_arg Subgraph.verts h
    have adj_eq := congr_arg Subgraph.Adj h
    simp only [sup_verts, sup_Adj] at verts_eq adj_eq
    constructor
    · intro v hv
      rw [verts_eq]
      exact Set.mem_union_left _ hv
    · intro v w hvw
      rw [adj_eq] at hvw
      exact hvw.elim id id
  · ext v
    · simp only [h.1]
    · simp only
      constructor
      · exact h.2 v v'
      · intro hvw
        cases hvw
        · exact hvw
        · have hv : v ∈ G₁.verts := by
            apply G₁.edge_vert_fst hvw
          have hw : v' ∈ G₁.verts := by
            apply G₁.edge_vert_snd hvw
          have := h.1 v hv
          have := h.1 v' hw
          exact h.2 v v' hvw

instance (G : Digraph V) : PartialOrder (G.Subgraph) where
  le := (· ≤ ·)
  le_refl _ := ⟨Set.Subset.refl _, fun _ _ h ↦ h⟩
  le_trans _ _ _ ⟨hv12, he12⟩ ⟨hv23, he23⟩ := ⟨Set.Subset.trans hv12 hv23, fun _ _ h ↦ he23 _ _ (he12 _ _ h)⟩
  le_antisymm _ _ ⟨hv12, he12⟩ ⟨hv21, he21⟩ := by
    ext v
    · exact Set.Subset.antisymm hv12 hv21
    · simp only
      constructor
      · exact he12 v v'
      · exact he21 v v'

instance (G : Digraph V) : SemilatticeInf (G.Subgraph) where
  inf := (· ⊓ ·)
  inf_le_left _ _ := ⟨Set.inter_subset_left _ _, fun _ _ ⟨h, _⟩ ↦ h⟩
  inf_le_right _ _ := ⟨Set.inter_subset_right _ _, fun _ _ ⟨_, h⟩ ↦ h⟩
  le_inf _ _ _ ⟨hv1, he1⟩ ⟨hv2, he2⟩ :=
    ⟨Set.subset_inter hv1 hv2, fun _ _ h ↦ ⟨he1 _ _ h, he2 _ _ h⟩⟩

instance (G : Digraph V) : SemilatticeSup (G.Subgraph) where
  sup := (· ⊔ ·)
  le_sup_left _ _ := ⟨Set.subset_union_left _ _, fun _ _ h ↦ Or.inl h⟩
  le_sup_right _ _ := ⟨Set.subset_union_right _ _, fun _ _ h ↦ Or.inr h⟩
  sup_le _ _ _ ⟨hv1, he1⟩ ⟨hv2, he2⟩ :=
    ⟨Set.union_subset hv1 hv2, fun _ _ h ↦ h.elim (he1 _ _) (he2 _ _)⟩

instance (G : Digraph V) : Lattice (G.Subgraph) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le_sup_left := SemilatticeSup.le_sup_left
  le_sup_right := SemilatticeSup.le_sup_right
  sup_le := SemilatticeSup.sup_le
  inf_le_left := SemilatticeInf.inf_le_left
  inf_le_right := SemilatticeInf.inf_le_right
  le_inf := SemilatticeInf.le_inf

instance (G : Digraph V) : BoundedOrder (G.Subgraph) where
  bot := (⊥ : G.Subgraph)
  bot_le _ := ⟨Set.empty_subset _, fun _ _ h ↦ False.elim h⟩
  top := (⊤ : G.Subgraph)
  le_top _ := ⟨Set.subset_univ _, fun _ _ h ↦ G₁.adj_sub h⟩

end Subgraph

end Digraph
