/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

-/

public section

/-- `HasSourceTarget V D` is a typeclass with two functions `src : D → V` and `tgt : D → V` that
  give the source and target of a dart. -/
class HasSourceTarget (V D : Type*) where
  /-- The first vertex of a dart. -/
  src : D → V
  /-- The second vertex of a dart. -/
  tgt : D → V

/-- Convert a dart to a pair of vertices. -/
@[expose] def HasSourceTarget.toProd {V D : Type*} [HasSourceTarget V D] (d : D) : V × V :=
  (HasSourceTarget.src d, HasSourceTarget.tgt d)

/-- `HasEdge D E` is a typeclass with a function `edge : D → E` that gives the edge of a dart. -/
class HasEdge (D E : Type*) where
  /-- The edge of a dart. -/
  edge : D → E

open HasSourceTarget HasEdge

/-- The `GraphLike` typeclass abstracts over graph-like structures by encoding the minimal structure
required to reason about directed edges ("darts") and adjacency. The "darts" terminology comes from
combinatorial maps, and they are also known as "half-edges" or "bonds." -/
class GraphLike (V D E : outParam Type*) [HasSourceTarget V D] [HasEdge D E] (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Gr → Set V
  /-- The set of darts (oriented edges) of a graph-like structure. -/
  darts : Gr → Set D
  /-- The set of edges of a graph-like structure. -/
  edges : Gr → Set E
  src_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → src d ∈ verts G
  tgt_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → tgt d ∈ verts G
  edge_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → edge d ∈ edges G
  /-- The adjacency relation of a graph-like structure. -/
  Adj : Gr → V → V → Prop := fun G u v ↦ ∃ d ∈ darts G, src d = u ∧ tgt d = v
  /-- Two vertices are adjacent if and only if there is a dart between them. -/
  exists_darts_iff_adj : ∀ ⦃G u v⦄, (∃ d ∈ darts G, src d = u ∧ tgt d = v) ↔ Adj G u v

namespace GraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc darts]
scoped notation "D(" G ")" => darts G

@[inherit_doc edges]
scoped notation "E(" G ")" => edges G

variable {V D E Gr : Type*} {G : Gr} {u u' v v' w : V} {d : D} {e : E}

section GraphLike

variable [HasSourceTarget V D] [HasEdge D E] [GraphLike V D E Gr]

lemma adj_of_mem_darts (hd : d ∈ D(G)) : Adj G (src d) (tgt d) :=
  exists_darts_iff_adj.mp ⟨d, hd, rfl, rfl⟩

lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact src_mem_of_darts hd

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact tgt_mem_of_darts hd

/-- The step from `u` to `v` is a dart from `u` to `v`. -/
@[expose]
def step (G : Gr) [GraphLike V D E Gr] (u v : V) := {d : D // d ∈ D(G) ∧ src d = u ∧ tgt d = v}

instance [DecidableEq D] : DecidableEq (step G u v) := Subtype.instDecidableEq

@[simp]
lemma step.src (h : step G u v) : src h.val = u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hu

@[simp]
lemma step.tgt (h : step G u v) : tgt h.val = v := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hv

lemma step.left_mem (h : step G u v) : u ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact src_mem_of_darts hd

lemma step.right_mem (h : step G u v) : v ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact tgt_mem_of_darts hd

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
@[expose] def step.todart (h : step G u v) : darts G := ⟨h.val, h.prop.1⟩

lemma step.todart_val (h : step G u v) : h.todart.val = h.val := by simp [step.todart]

lemma step.todart_src (s : step G u v) : HasSourceTarget.src s.todart.val = u := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.todart_tgt (s : step G u v) : HasSourceTarget.tgt s.todart.val = v := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma step.adj (h : step G u v) : Adj G u v := by
  rw [← exists_darts_iff_adj]
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨d, hd, rfl, rfl⟩

@[ext] theorem darts_ext (d₁ d₂ : darts G) (h : d₁.val = d₂.val) : d₁ = d₂ := Subtype.ext h

/-- Convert a dart to a step. -/
@[expose] def dartStep (d : darts G) : step G (src d.val) (tgt d.val) := ⟨d.val, d.prop, rfl, rfl⟩

@[simp]
lemma dartStep_val (d : darts G) : (dartStep d).val = d.val := by simp [dartStep]

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
@[expose] def DartAdj (d d' : darts G) : Prop := (tgt d.val : V) = (src d'.val : V)

section GraphLikeProd

/-
### For `GraphLike V (V × V) (Sym2 V) Gr`

Some graph-like structures, such as `SimpleGraph` and `Digraph`, have `V × V`-valued darts.
This section assumes `GraphLike V (V × V) (Sym2 V) Gr` to proves lemmas for `V × V`-valued darts.
-/

variable {d : V × V}

instance : HasSourceTarget V (V × V) where
  src := Prod.fst
  tgt := Prod.snd

@[simp, grind =] lemma src_eq : src d = d.fst := rfl

@[simp, grind =] lemma tgt_eq : tgt d = d.snd := rfl

@[simp] lemma toProd_eq : toProd d = d := rfl

instance : HasEdge (V × V) (Sym2 V) where
  edge d := s(d.fst, d.snd)

@[simp, grind =] lemma edge_eq : edge d = s(d.fst, d.snd) := rfl

instance : HasEdge (V × V) (V × V) where
  edge := id

@[simp, grind =] lemma edge_eq' : edge d = d := rfl

variable [GraphLike V (V × V) (Sym2 V) Gr]

@[simp]
lemma mem_darts_iff_adj : d ∈ darts G ↔ Adj G d.fst d.snd := by
  simp [← exists_darts_iff_adj, src_eq, tgt_eq]

instance [DecidableRel (Adj G)] : DecidablePred (· ∈ darts G) :=
  fun d => decidable_of_iff (Adj G (src d) (tgt d)) (mem_darts_iff_adj.symm)

/-- If `u` and `v` are adjacent, then there exists a step from `u` to `v`. -/
@[expose] def Adj.toStep (h : Adj G u v) : step G u v := ⟨(u, v), mem_darts_iff_adj.mpr h, rfl, rfl⟩

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
