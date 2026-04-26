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

-/

public section

/-- The `GraphLike` typeclass abstracts over graph-like structures by encoding the minimal structure
required to reason about directed edges ("darts") and adjacency. The "darts" terminology comes from
combinatorial maps, and they are also known as "half-edges" or "bonds." -/
class GraphLike (V D : outParam Type*) {Gr : Type*} (G : Gr) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Set V
  /-- The set of darts (oriented edges) of a graph-like structure. -/
  darts : Set D
  /-- The first/source vertex of a dart. -/
  fst : D → V
  /-- The second/target vertex of a dart. -/
  snd : D → V
  fst_mem_of_darts : ∀ ⦃d⦄, d ∈ darts → fst d ∈ verts
  snd_mem_of_darts : ∀ ⦃d⦄, d ∈ darts → snd d ∈ verts
  /-- The adjacency relation of a graph-like structure. -/
  Adj : V → V → Prop := fun u v ↦ ∃ d ∈ darts, fst d = u ∧ snd d = v
  /-- Two vertices are adjacent if and only if there is a dart between them. -/
  exists_darts_iff_adj : ∀ ⦃u v⦄, (∃ d ∈ darts, fst d = u ∧ snd d = v) ↔ Adj u v

namespace GraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc darts]
scoped notation "D(" G ")" => darts G

variable {V D Gr : Type*} {G : Gr} {u u' v v' w : V} {d : D}

section GraphLike

variable [GraphLike V D G]

lemma adj_of_mem_darts (hd : d ∈ D(G)) : Adj G (fst G d) (snd G d) :=
  exists_darts_iff_adj.mp ⟨d, hd, rfl, rfl⟩

lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact fst_mem_of_darts hd

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact snd_mem_of_darts hd

/-- Convert a dart to a pair of vertices. -/
@[expose] def toProd (d : D(G)) : V × V := (fst G d.val, snd G d.val)

/-- The step from `u` to `v` is a dart from `u` to `v`. -/
@[expose]
def step (G : Gr) [GraphLike V D G] (u v : V) := {d : D // d ∈ D(G) ∧ fst G d = u ∧ snd G d = v}

instance [DecidableEq D] : DecidableEq (step G u v) := Subtype.instDecidableEq

@[simp]
lemma step.fst (h : step G u v) : fst G h.val = u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hu

@[simp]
lemma step.snd (h : step G u v) : snd G h.val = v := by
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

lemma step.todart_val (h : step G u v) : h.todart.val = h.val := by simp [step.todart]

lemma step.todart_fst (s : step G u v) : GraphLike.fst G s.todart.val = u := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.todart_snd (s : step G u v) : GraphLike.snd G s.todart.val = v := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.adj (h : step G u v) : Adj G u v := by
  rw [← exists_darts_iff_adj]
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨d, hd, rfl, rfl⟩

@[ext] theorem darts_ext (d₁ d₂ : darts G) (h : d₁.val = d₂.val) : d₁ = d₂ := Subtype.ext h

/-- Convert a dart to a step. -/
def dartStep (d : darts G) : step G (fst G d.val) (snd G d.val) :=
  ⟨d.val, d.prop, rfl, rfl⟩

@[simp]
lemma dartStep_val (d : darts G) : (dartStep d).val = d.val := by simp [dartStep]

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
@[expose] def DartAdj (d d' : darts G) : Prop := (snd G d.val : V) = (fst G d'.val : V)


section SimpleGraphLike

/-
### For `GraphLike V (V × V) G`

Some graph-like structures, such as `SimpleGraph` and `Digraph`, have `V × V`-valued darts.
This section defines `SimpleGraphLike` to give a simplified constructor for `GraphLike V (V × V) G`
and proves lemmas for `V × V`-valued darts.
-/

variable {d : V × V} {Gr : Type _ → Type*} {G : Gr V}

/-- `SimpleGraphLike` is a simplified constructor for `GraphLike V (V × V) G`. -/
class SimpleGraphLike {Gr : Type _ → Type*} (G : Gr V) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Set V
  /-- The set of darts (oriented edges) of a graph-like structure. -/
  darts : Set (V × V)
  /-- The first/source vertex of a dart is in the set of vertices. -/
  fst_mem_of_darts : ∀ ⦃d⦄, d ∈ darts → d.fst ∈ verts
  /-- The second/target vertex of a dart is in the set of vertices. -/
  snd_mem_of_darts : ∀ ⦃d⦄, d ∈ darts → d.snd ∈ verts
  /-- The adjacency relation of a graph-like structure. -/
  Adj : V → V → Prop := fun u v ↦ ∃ d ∈ darts, d.fst = u ∧ d.snd = v
  /-- Two vertices are adjacent if and only if there is a dart between them. -/
  exists_darts_iff_adj : ∀ ⦃u v⦄, (∃ d ∈ darts, d.fst = u ∧ d.snd = v) ↔ Adj u v

instance [SimpleGraphLike G] : GraphLike V (V × V) G where
  verts := SimpleGraphLike.verts G
  darts := SimpleGraphLike.darts G
  fst := Prod.fst
  snd := Prod.snd
  fst_mem_of_darts := SimpleGraphLike.fst_mem_of_darts
  snd_mem_of_darts := SimpleGraphLike.snd_mem_of_darts
  Adj := SimpleGraphLike.Adj G
  exists_darts_iff_adj := SimpleGraphLike.exists_darts_iff_adj

variable [SimpleGraphLike G]

@[simp, grind =] lemma fst_eq : fst G d = d.fst := rfl

@[simp, grind =] lemma snd_eq : snd G d = d.snd := rfl

@[simp]
lemma mem_darts_iff_adj : d ∈ darts G ↔ Adj G d.fst d.snd := by
  simp [← exists_darts_iff_adj, fst, snd]

instance [DecidableRel (Adj G)] : DecidablePred (· ∈ darts G) :=
  fun d => decidable_of_iff (Adj G (fst G d) (snd G d)) (mem_darts_iff_adj.symm)

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

end SimpleGraphLike

end GraphLike.GraphLike
