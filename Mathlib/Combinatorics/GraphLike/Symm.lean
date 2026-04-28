/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `SymmDartLike`: extends `DartLike` for darts with an inverse.
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

public section

/-- `HasInvol D` is a typeclass with a function `symm : D → D` that gives the inverse of a dart. -/
class HasInvol (D : Type*) where
  /-- The inverse of a dart. -/
  symm : D → D
  symm_invol : ∀ ⦃d⦄, symm (symm d) = d

/-- `SymmDartLike` extends `HasSourceTarget` and `HasInvol` for darts that are symmetric. -/
class SymmDartLike (V D : Type*) extends HasSourceTarget V D, HasInvol D where
  symm_fst (d : D) : src (symm d) = (tgt d : V)
  symm_snd (d : D) : tgt (symm d) = (src d : V)

open HasSourceTarget HasEdge HasInvol SymmDartLike

/-- `SymmGraphLike` extends `GraphLike` for graph-like structures where darts are symmetric. -/
class SymmGraphLike (V D E : outParam Type*) [HasEdge D E] [SymmDartLike V D]
    (Gr : Type*) extends GraphLike V D E Gr where
  /-- The inverse of a dart. -/
  symm_ne : ∀ ⦃G d⦄, d ∈ darts G → symm d ≠ d
  symm_mem_darts_iff : ∀ ⦃G d⦄, symm d ∈ darts G ↔ d ∈ darts G
  edge_eq_edge_iff : ∀ ⦃G d d'⦄, d ∈ darts G → d' ∈ darts G →
    ((edge d : E) = edge d' ↔ d = d' ∨ symm d = d')

open SymmGraphLike

attribute [simp, grind =] symm_invol symm_fst symm_snd symm_mem_darts_iff
attribute [grind →] symm_ne

variable {V D E Gr : Type*} {G : Gr} {u v w : V} {d : D}

namespace GraphLike

variable [HasEdge D E] [SymmDartLike V D] [SymmGraphLike V D E Gr]

lemma symm_mem_darts (hd : d ∈ darts G) : symm d ∈ darts G :=
  symm_mem_darts_iff.mpr hd

/-- The inverse of a step. -/
@[symm] def step.symm (h : step G u v) : step G v u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  use HasInvol.symm d, symm_mem_darts hd, hv ▸ symm_fst d, hu ▸ symm_snd d

@[simp]
lemma step.symm_symm (h : step G u v) : h.symm.symm = h := by
  obtain ⟨d, hd, hu, hv⟩ := h
  change step.symm (⟨HasInvol.symm d, symm_mem_darts hd, hv ▸ symm_fst d, hu ▸ symm_snd d⟩ :
    step G v u) = _
  simp [symm]

instance : Std.Symm (Adj G) where
  symm _ _ h := by
    rw [← exists_darts_iff_adj] at h ⊢
    obtain ⟨d, hd, rfl, rfl⟩ := h
    exact ⟨HasInvol.symm d, symm_mem_darts hd, symm_fst d, symm_snd d⟩

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

/-- The two vertices of the dart as an unordered pair. -/
@[expose] def dartSym2 (d : darts G) : Sym2 V := s(src d.val, tgt d.val)

@[simp]
theorem dartSym2_mk (h : d ∈ darts G) : dartSym2 (⟨d, h⟩ : darts G) = s(src d, tgt d) := rfl

/-- The dart with reversed orientation from a given dart. -/
@[expose] def dartSymm (d : darts G) : darts G := ⟨symm d.val, symm_mem_darts_iff.mpr d.prop⟩

@[simp]
theorem dartSymm_mk (h : d ∈ darts G) : dartSymm (⟨d, h⟩) = ⟨symm d, symm_mem_darts_iff.mpr h⟩ :=
  rfl

@[simp]
theorem dartSym2_symm (d : darts G) : dartSym2 (dartSymm d) = dartSym2 d := by
  simp [dartSym2, dartSymm]

@[simp]
theorem dartSym2_comp_symm : dartSym2 ∘ dartSymm = (dartSym2 : darts G → Sym2 _) :=
  funext dartSym2_symm

@[simp]
theorem dartSymm_dartSymm (d : darts G) : dartSymm (dartSymm d) = d :=
  darts_ext _ _ <| by simp [dartSymm]

@[simp]
theorem dartSymm_involutive : Function.Involutive (dartSymm : darts G → darts G) :=
  dartSymm_dartSymm

theorem dartSym2_eq_mk'_iff {d : darts G} :
    dartSym2 d = s(u, v) ↔ toProd d = (u, v) ∨ toProd d = (v, u) := by
  obtain ⟨p, hp⟩ := d
  simp [toProd]

theorem dartSym2_eq_mk'_iff' {d : darts G} : dartSym2 d = s(u, v) ↔
    src d.val = u ∧ tgt d.val = v ∨ src d.val = v ∧ tgt d.val = u := by
  obtain ⟨p, hp⟩ := d
  simp

section GraphLikeProd

/-
### For `SymmGraphLike V (V × V) (Sym2 V) Gr`
-/

variable {d : V × V} {Gr : Type*} {G : Gr}

instance : SymmDartLike V (V × V) where
  symm := Prod.swap
  symm_invol := Prod.swap_swap
  symm_fst d := by simp
  symm_snd d := by simp

variable [SymmGraphLike V (V × V) (Sym2 V) Gr]

@[simp, grind =] lemma symm_apply (d : V × V) : HasInvol.symm d = Prod.swap d := rfl

lemma Adj.ne (h : Adj G u v) : u ≠ v := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨⟨u, v⟩, hd, rfl, rfl⟩ := h
  grind [symm_ne hd]

instance : Std.Irrefl (Adj G) where
  irrefl _ h := h.ne rfl

end GraphLike.GraphLikeProd
