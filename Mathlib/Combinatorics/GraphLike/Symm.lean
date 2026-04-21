/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Data.Sym.Sym2

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

/-- `SymmGraphLike` extends `GraphLike` for graph-like structures where darts are symmetric. -/
class SymmGraphLike (V D : outParam Type*) {Gr : Type*} (G : Gr) extends GraphLike V D G where
  symm : D → D
  symm_invol : ∀ ⦃d⦄, symm (symm d) = d
  symm_ne : ∀ ⦃d⦄, d ∈ darts → symm d ≠ d
  symm_fst (d) : fst (symm d) = snd d
  symm_snd (d) : snd (symm d) = fst d
  symm_mem_darts_iff : ∀ ⦃d⦄, symm d ∈ darts ↔ d ∈ darts

attribute [simp] SymmGraphLike.symm_invol SymmGraphLike.symm_ne SymmGraphLike.symm_fst
  SymmGraphLike.symm_snd SymmGraphLike.symm_mem_darts_iff

open SymmGraphLike
namespace GraphLike

variable {V D Gr : Type*} {G : Gr} {u v w : V} {d : D}

section SymmGraphLike

variable [SymmGraphLike V D G]

lemma symm_mem_darts (hd : d ∈ darts G) : symm G d ∈ darts G :=
  symm_mem_darts_iff.mpr hd

/-- The inverse of a step. -/
@[symm] def step.symm (h : step G u v) : step G v u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  use SymmGraphLike.symm G d, symm_mem_darts hd, hv ▸ symm_fst d, hu ▸ symm_snd d

@[simp]
lemma step.symm_symm (h : step G u v) : h.symm.symm = h := by
  obtain ⟨d, hd, hu, hv⟩ := h
  change step.symm (⟨SymmGraphLike.symm G d, symm_mem_darts hd, hv ▸ symm_fst d, hu ▸ symm_snd d⟩ :
    step G v u) = _
  simp [symm]

instance : Std.Symm (Adj G) where
  symm _ _ h := by
    rw [← exists_darts_iff_adj] at h ⊢
    obtain ⟨d, hd, rfl, rfl⟩ := h
    exact ⟨SymmGraphLike.symm G d, symm_mem_darts hd, symm_fst d, symm_snd d⟩

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

/-- The two vertices of the dart as an unordered pair. -/
@[expose] def dartSym2 (d : darts G) : Sym2 V := s(fst G d.val, snd G d.val)

@[simp]
theorem dartSym2_mk (h : d ∈ darts G) : dartSym2 (⟨d, h⟩ : darts G) = s(fst G d, snd G d) := rfl

/-- The dart with reversed orientation from a given dart. -/
@[expose] def dartSymm (d : darts G) : darts G := ⟨symm G d.val, symm_mem_darts_iff.mpr d.prop⟩

@[simp]
theorem dartSymm_mk (h : d ∈ darts G) : dartSymm (⟨d, h⟩) = ⟨symm G d, symm_mem_darts_iff.mpr h⟩ :=
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
    fst G d.val = u ∧ snd G d.val = v ∨ fst G d.val = v ∧ snd G d.val = u := by
  obtain ⟨p, hp⟩ := d
  simp

end SymmGraphLike

section GraphLikeProd

/-
### For `SimpleGraphLike G`

This section defines `SimpleSymmGraphLike` to give a simplified constructor for `SimpleGraphLike G`
that is symmetric in the sense that `d` and `d.swap` are both in the set of darts.
-/

variable {d : V × V} {Gr : Type _ → Type*} {G : Gr V}

class SimpleSymmGraphLike (G : Gr V) extends SimpleGraphLike G where
  symm_mem_darts_iff : ∀ ⦃d⦄, d.swap ∈ darts ↔ d ∈ darts

instance [SimpleSymmGraphLike G] : SymmGraphLike V (V × V) G where
  symm := Prod.swap
  symm_invol := Prod.swap_swap
  symm_ne d hd heq := by
    obtain ⟨a, b⟩ := d
    grind [(mem_darts_iff_adj.mp hd).ne]
  symm_fst d := Prod.fst_swap
  symm_snd d := Prod.snd_swap
  symm_mem_darts_iff := SimpleSymmGraphLike.symm_mem_darts_iff

end GraphLikeProd
end GraphLike
