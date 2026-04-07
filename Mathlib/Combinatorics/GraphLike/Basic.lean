/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Sigma

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `DartLike`: is the typeclass for capturing the common structure of darts.
* `GraphLike`: is the main typeclass for capturing the common notion of graphs.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `dart` gives the type of darts, which is an oriented edge, of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.
* `darts G` is the direct generalization of `Dart` in `SimpleGraph`.

## Notes

* `GraphLike α β` generalizes `SimpleGraph`, `Digraph`, and `Graph`. When multi-digraph,
  hypergraphs and other kinds of graphs are formalized, they can also use this typeclass.
* `GraphLike α (α × α)` generalizes `SimpleGraph` and `Digraph` but not `Graph`.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.
-/

@[expose] public section

/-- The typeclass `DartLike α β` captures the common structure of darts. -/
class DartLike (α β : Type*) where
  /-- The first vertex of a dart. -/
  fst : β → α
  /-- The second vertex of a dart. -/
  snd : β → α

/-- Convert a dart to a pair of vertices. -/
def DartLike.toProd {α β : Type*} [DartLike α β] (d : β) : α × α := (DartLike.fst d, DartLike.snd d)

/-- The `GraphLike` typeclass abstracts over graph-like structures by encoding the minimal structure
required to reason about directed edges ("darts") and adjacency. The "darts" terminology comes from
combinatorial maps, and they are also known as "half-edges" or "bonds." -/
class GraphLike (α β : outParam Type*) [DartLike α β] (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Gr → Set α
  /-- The set of darts (oriented edges) of a graph-like structure. -/
  darts : Gr → Set β
  fst_mem_of_darts {G : Gr} {d : β} : d ∈ darts G → DartLike.fst d ∈ verts G
  snd_mem_of_darts {G : Gr} {d : β} : d ∈ darts G → DartLike.snd d ∈ verts G
  /-- The adjacency relation of a graph-like structure. -/
  Adj : Gr → α → α → Prop := fun G u v ↦ ∃ d ∈ darts G, DartLike.fst d = u ∧ DartLike.snd d = v
  exists_darts_iff_adj {G : Gr} {u v : α} :
    (∃ d ∈ darts G, DartLike.fst d = u ∧ DartLike.snd d = v) ↔ Adj G u v

open DartLike
namespace GraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

variable {V D Gr : Type*} {G : Gr} {u u' v v' w : V} {d : D}

section GraphLike

variable [DartLike V D] [GraphLike V D Gr]

lemma adj_of_mem_darts (hd : d ∈ darts G) : Adj G (fst d) (snd d) :=
  exists_darts_iff_adj.mp ⟨d, hd, rfl, rfl⟩

lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact fst_mem_of_darts hd

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact snd_mem_of_darts hd

/-- The step from `u` to `v` is a dart from `u` to `v`. -/
def step (G : Gr) (u v : V) := {d : D // d ∈ darts G ∧ fst d = u ∧ snd d = v}

instance [DecidableEq D] : DecidableEq (step G u v) := Subtype.instDecidableEq

@[simp]
lemma step.fst (h : step G u v) : fst h.val = u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hu

@[simp]
lemma step.snd (h : step G u v) : snd h.val = v := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hv

lemma step.left_mem (h : step G u v) : u ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact fst_mem_of_darts hd

lemma step.right_mem (h : step G u v) : v ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact snd_mem_of_darts hd

lemma step.left_eq_of_val_eq {s₁ : step G u v} {s₂ : step G u' v'} (h : s₁.val = s₂.val) :
    u = u' := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

lemma step.right_eq_of_val_eq {s₁ : step G u v} {s₂ : step G u' v'} (h : s₁.val = s₂.val) :
    v = v' := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

@[ext] lemma step.ext {s₁ s₂ : step G u v} (h : s₁.val = s₂.val) : s₁ = s₂ := Subtype.ext h

attribute [simp] step.ext_iff

@[simp]
lemma step.ext_HEq {u' v'} {s₁ : step G u v} {s₂ : step G u' v'} (h : s₁.val = s₂.val) :
    s₁ ≍ s₂ := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

/-- Convert a step to a dart. -/
def step.todart (h : step G u v) : darts G := ⟨h.val, h.prop.1⟩

@[simp]
lemma step.todart_val (h : step G u v) : h.todart.val = h.val := rfl

lemma step.todart_fst (s : step G u v) : DartLike.fst s.todart.val = u := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.todart_snd (s : step G u v) : DartLike.snd s.todart.val = v := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.adj (h : step G u v) : Adj G u v := by
  rw [← exists_darts_iff_adj]
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨d, hd, rfl, rfl⟩

@[ext] theorem darts_ext (d₁ d₂ : darts G) (h : d₁.val = d₂.val) : d₁ = d₂ := Subtype.ext h

/-- Convert a dart to a step. -/
def dartStep (d : darts G) : step G (fst d.val) (snd d.val) :=
  ⟨d.val, d.prop, rfl, rfl⟩

@[simp]
lemma dartStep_val (d : darts G) : (dartStep d).val = d.val := rfl

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : darts G) : Prop := (snd d.val : V) = (fst d'.val : V)

section GraphLikeProd

/-
### For `GraphLike α (α × α) Gr`

Some graph-like structures, such as `SimpleGraph` and `Digraph`, have `α × α`-valued darts.
This section assumes `GraphLike α (α × α) Gr` to proves lemmas for `α × α`-valued darts.
-/

variable {d : V × V}

instance : DartLike V (V × V) where
  fst := Prod.fst
  snd := Prod.snd

@[simp, grind =] lemma fst_eq : fst d = d.fst := rfl

@[simp, grind =] lemma snd_eq : snd d = d.snd := rfl

@[simp] lemma toProd_eq : toProd d = d := rfl

variable [GraphLike V (V × V) Gr]

@[simp]
lemma mem_darts_iff_adj : d ∈ darts G ↔ Adj G d.fst d.snd := by
  simp [← exists_darts_iff_adj, fst, snd]

instance [DecidableRel (Adj G)] : DecidablePred (· ∈ darts G) :=
  fun d => decidable_of_iff (Adj G (fst d) (snd d)) (mem_darts_iff_adj.symm)

/-- If `u` and `v` are adjacent, then there exists a step from `u` to `v`. -/
def Adj.toStep (h : Adj G u v) : step G u v := ⟨(u, v), mem_darts_iff_adj.mpr h, rfl, rfl⟩

instance : Subsingleton (step G u v) where
  allEq := by
    rintro ⟨p₁, h₁, rfl, rfl⟩ ⟨p₂, h₂, h1, h2⟩
    obtain rfl := Prod.ext h1 h2
    exact Subtype.ext rfl

@[simp]
lemma val_step_eq {s : step G u v} : s.val = (u, v) := by
  rw [Subsingleton.elim s s.adj.toStep]
  rfl

end GraphLikeProd

end GraphLike.GraphLike
