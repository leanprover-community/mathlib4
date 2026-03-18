/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sym.Sym2

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `DartLike`: is the typeclass for capturing the common structure of darts.
* `SymmDartLike`: extends `DartLike` for darts with an inverse.
* `GraphLike`: is the main typeclass for capturing the common structure of graph-like structures.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `dart` gives the type of darts, which is an oriented edge, of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.
* `SymmGraphLike`: extends `GraphLike` for graph-like structures with symmetric darts.
* `darts G` is the direct generalization of `Dart` in `SimpleGraph`. A couple functions, `dartSym2`
   and `dartSymm`, are generalized from `SimpleGraph.Dart` to here.

## Notes

* `GraphLike α β` generalizes `SimpleGraph`, `Digraph`, and `Graph`. When multi-digraph and
  hypergraphs are formalized, they can also use this typeclass.
* `SymmGraphLike α β` generalizes `SimpleGraph` and `Graph` but not `Digraph`.
* `GraphLike α (α × α)` generalizes `SimpleGraph` and `Digraph` but not `Graph`.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.
* Define the degree of a graph.
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

/-- The typeclass `SymmDartLike α β` captures the common structure of darts with symmetry. -/
class SymmDartLike (α β : Type*) extends DartLike α β where
  /-- The inverse of a dart. -/
  inv : β → β
  /-- The inverse of the inverse of a dart is the dart itself. -/
  inv_invol {d : β} : inv (inv d) = d
  /-- The first vertex of the inverse of a dart is the second vertex of the dart. -/
  inv_fst {d : β} : fst (inv d) = snd d
  /-- The second vertex of the inverse of a dart is the first vertex of the dart. -/
  inv_snd {d : β} : snd (inv d) = fst d

attribute [simp] SymmDartLike.inv_invol SymmDartLike.inv_fst SymmDartLike.inv_snd

/-- The `GraphLike` typeclass abstracts over graph-like structures by encoding the minimal structure
required to reason about directed edges ("darts") and adjacency. This terminology comes from
combinatorial maps, and they are also known as "half-edges" or "bonds." -/
class GraphLike (α β : outParam Type*) [DartLike α β] (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Gr → Set α
  /-- The type of darts (oriented edges) of a graph-like structure. -/
  darts : Gr → Set β
  fst_mem_of_darts : ∀ {G : Gr} {d : β}, d ∈ darts G → DartLike.fst d ∈ verts G
  snd_mem_of_darts : ∀ {G : Gr} {d : β}, d ∈ darts G → DartLike.snd d ∈ verts G
  /-- The adjacency relation of a graph-like structure. -/
  Adj : Gr → α → α → Prop := fun G u v ↦ ∃ d ∈ darts G, DartLike.fst d = u ∧ DartLike.snd d = v
  exists_darts_iff_adj {G : Gr} {u v : α} :
    (∃ d ∈ darts G, DartLike.fst d = u ∧ DartLike.snd d = v) ↔ Adj G u v

/-- `SymmGraphLike` extends `GraphLike` for graph-like structures where darts are symmetric. -/
class SymmGraphLike (α β : outParam Type*) [SymmDartLike α β] (Gr : Type*)
    extends GraphLike α β Gr where
  inv_mem_darts_iff {G : Gr} {d : β} : SymmDartLike.inv α d ∈ darts G ↔ d ∈ darts G

attribute [simp] SymmGraphLike.inv_mem_darts_iff

open DartLike SymmDartLike GraphLike SymmGraphLike
namespace GraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

variable {α β Gr : Type*} {G : Gr} {u v w : α} {d : β}

section GraphLike

variable [DartLike α β] [GraphLike α β Gr]

/-- Dot notation for reverse direction of `adj_iff_nonempty_dart`. -/
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
def step (G : Gr) (u v : α) := {d : β // d ∈ darts G ∧ fst d = u ∧ snd d = v}

instance [DecidableEq β] : DecidableEq (step G u v) := Subtype.instDecidableEq

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

lemma step.left_eq_of_val {u' v' : α} {s₁ : step G u v} {s₂ : step G u' v'} (h : s₁.val = s₂.val) :
    u = u' := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

lemma step.right_eq_of_val {u' v' : α} {s₁ : step G u v} {s₂ : step G u' v'} (h : s₁.val = s₂.val) :
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

lemma step.adj (h : step G u v) : Adj G u v := by
  rw [← exists_darts_iff_adj]
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨d, hd, rfl, rfl⟩

@[ext] theorem darts_ext (d₁ d₂ : darts G) (h : d₁.val = d₂.val) : d₁ = d₂ := Subtype.ext h

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : darts G) : Prop := (snd d.val : α) = (fst d'.val : α)

end GraphLike

section SymmGraphLike

variable [SymmDartLike α β] [SymmGraphLike α β Gr]

lemma inv_mem_darts (hd : d ∈ darts G) : inv α d ∈ darts G :=
  inv_mem_darts_iff.mpr hd

/-- The inverse of a step. -/
def step.inv (h : step G u v) : step G v u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  use SymmDartLike.inv α d, inv_mem_darts hd, hv ▸ inv_fst, hu ▸ inv_snd

@[simp]
lemma step.inv_inv (h : step G u v) : h.inv.inv = h := by
  obtain ⟨d, hd, hu, hv⟩ := h
  change step.inv (⟨SymmDartLike.inv α d, inv_mem_darts hd, hv ▸ inv_fst, hu ▸ inv_snd⟩ :
    step G v u) = _
  simp [inv]

instance : Std.Symm (Adj G) where
  symm _ _ h := by
    rw [← exists_darts_iff_adj] at h ⊢
    obtain ⟨d, hd, rfl, rfl⟩ := h
    exact ⟨SymmDartLike.inv α d, inv_mem_darts hd, inv_fst, inv_snd⟩

lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

/-- The two vertices of the dart as an unordered pair. -/
def dartSym2 (d : darts G) : Sym2 α := s(fst d.val, snd d.val)

@[simp]
theorem dartSym2_mk {p : β} (h : p ∈ darts G) : dartSym2 (⟨p, h⟩ : darts G) = s(fst p, snd p) :=
  rfl

/-- The dart with reversed orientation from a given dart. -/
def dartSymm (d : darts G) : darts G := ⟨inv α d.val, inv_mem_darts_iff.mpr d.prop⟩

@[simp]
theorem dartSymm_mk {p : β} (h : p ∈ darts G) :
    dartSymm (⟨p, h⟩) = ⟨inv α p, inv_mem_darts_iff.mpr h⟩ :=
  rfl

@[simp]
theorem dartSym2_symm (d : darts G) : dartSym2 (dartSymm d) = dartSym2 d := by
  simp [dartSym2, dartSymm]

@[simp]
theorem dartSym2_comp_symm : dartSym2 ∘ dartSymm = (dartSym2 : darts G → Sym2 α) :=
  funext dartSym2_symm

@[simp]
theorem dartSymm_dartSymm (d : darts G) : dartSymm (dartSymm d) = d :=
  darts_ext _ _ <| inv_invol

@[simp]
theorem dartSymm_involutive : Function.Involutive (dartSymm : darts G → darts G) :=
  dartSymm_dartSymm

theorem dartSym2_eq_mk'_iff {d : darts G} :
    dartSym2 d = s(u, v) ↔ toProd d.val = (u, v) ∨ toProd d.val = (v, u) := by
  obtain ⟨p, hp⟩ := d
  simp [toProd]

theorem dartSym2_eq_mk'_iff' {d : darts G} :
    dartSym2 d = s(u, v) ↔ fst d.val = u ∧ snd d.val = v ∨ fst d.val = v ∧ snd d.val = u := by
  obtain ⟨p, hp⟩ := d
  rw [dartSym2_eq_mk'_iff]
  simp [toProd]

end SymmGraphLike

section GraphLikeProd

/-
### For `HasDart α (α × α) Gr`

Some graph-like structures, such as `SimpleGraph` and `Digraph`, have `α × α`-valued darts.
This section assumes `GraphLike α (α × α) Gr` to proves lemmas for `α × α`-valued darts.
-/

variable {d : α × α}

instance : SymmDartLike α (α × α) where
  fst := Prod.fst
  snd := Prod.snd
  inv := Prod.swap
  inv_invol := Prod.swap_swap _
  inv_fst := Prod.fst_swap
  inv_snd := Prod.snd_swap

@[simp] lemma fst_eq : fst d = d.fst := rfl

@[simp] lemma snd_eq : snd d = d.snd := rfl

@[simp] lemma toProd_eq : toProd d = d := rfl

@[simp] lemma inv_eq : inv α d = d.swap := rfl

variable [GraphLike α (α × α) Gr]

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
lemma step_val_eq {s : step G u v} : s.val = (u, v) := by
  rw [Subsingleton.elim s s.adj.toStep]
  rfl

end GraphLikeProd

theorem dartSym2_eq_iff [SymmGraphLike α (α × α) Gr] :
    ∀ d₁ d₂ : darts G, dartSym2 d₁ = dartSym2 d₂ ↔ d₁ = d₂ ∨ d₁ = dartSymm d₂ := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp

end GraphLike
