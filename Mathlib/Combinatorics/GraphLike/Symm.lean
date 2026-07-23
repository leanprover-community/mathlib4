/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `SymmGraphLike` for capturing the common structure of different
kinds of graph structures including `SimpleGraph` and `Graph` where darts are symmetric.

## Main definitions

* `SymmGraphLike`: extends `GraphLike` for graph-like structures with symmetric darts.
-/

public section

/-- `SymmGraphLike` extends `GraphLike` for graph-like structures where darts are symmetric. -/
class SymmGraphLike (V D E : outParam Type*) (Gr : Type*) extends GraphLike V D E Gr where
  /-- The inverse of a dart. -/
  inv : D → D
  inv_invol : ∀ ⦃d⦄, inv (inv d) = d
  inv_src (d : D) : src (inv d) = (tgt d : V)
  inv_tgt (d : D) : tgt (inv d) = (src d : V)
  inv_ne : ∀ ⦃G d⦄, d ∈ darts G → inv d ≠ d
  inv_mem_darts_iff : ∀ ⦃G d⦄, inv d ∈ darts G ↔ d ∈ darts G
  edge_eq_edge_iff : ∀ ⦃G d d'⦄, d ∈ darts G → d' ∈ darts G →
    ((edge d : E) = edge d' ↔ d = d' ∨ inv d = d')

open SymmGraphLike

attribute [simp, grind =] inv_invol inv_src inv_tgt inv_mem_darts_iff
attribute [grind →] inv_ne

variable {V D E Gr : Type*} {G : Gr} {u v w : V} {d : D}

namespace GraphLike

variable [SymmGraphLike V D E Gr]

lemma inv_mem_darts (hd : d ∈ darts G) : inv Gr d ∈ darts G :=
  inv_mem_darts_iff.mpr hd

/-- The inverse of a step. -/
@[symm] def step.inv (h : step G u v) : step G v u where
  val := SymmGraphLike.inv Gr h.val
  property := by
    obtain ⟨d, hd, hu, hv⟩ := h
    use inv_mem_darts hd, hv ▸ inv_src d, hu ▸ inv_tgt d

@[simp]
lemma step.inv_inv (h : step G u v) : h.inv.inv = h := by
  obtain ⟨d, hd, hu, hv⟩ := h
  change step.inv (⟨SymmGraphLike.inv Gr d, inv_mem_darts hd, hv ▸ inv_src d, hu ▸ inv_tgt d⟩ :
    step G v u) = _
  simp [inv]

instance : Std.Symm (Adj G) where
  symm _ _ h := by
    rw [← exists_darts_iff_adj] at h ⊢
    obtain ⟨d, hd, rfl, rfl⟩ := h
    exact ⟨SymmGraphLike.inv Gr d, inv_mem_darts hd, inv_src d, inv_tgt d⟩

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

/-- The two vertices of the dart as an unordered pair. -/
@[expose] def dartSym2 (d : darts G) : Sym2 V := s(src Gr d.val, tgt Gr d.val)

@[simp]
theorem dartSym2_mk (h : d ∈ darts G) : dartSym2 (⟨d, h⟩ : darts G) = s(src Gr d, tgt Gr d) := rfl

@[simp]
lemma step.todart_dartSym2 (h : step G u v) : dartSym2 h.todart = s(u, v) := by
  obtain ⟨d, hd, hu, hv⟩ := h
  grind [dartSym2, todart]

/-- The dart with reversed orientation from a given dart. -/
@[expose] def dartSymm (d : darts G) : darts G := ⟨inv Gr d.val, inv_mem_darts_iff.mpr d.prop⟩

@[simp]
theorem dartSymm_mk (h : d ∈ darts G) : dartSymm (⟨d, h⟩) = ⟨inv Gr d, inv_mem_darts_iff.mpr h⟩ :=
  rfl

@[simp]
lemma step.inv_todart (h : step G u v) : h.inv.todart = dartSymm h.todart := by
  simp [todart, step.inv]

@[simp]
theorem dartSym2_inv (d : darts G) : dartSym2 (dartSymm d) = dartSym2 d := by
  simp [dartSym2, dartSymm]

@[simp]
theorem dartSym2_comp_inv : dartSym2 ∘ dartSymm = (dartSym2 : darts G → Sym2 _) :=
  funext dartSym2_inv

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
    src Gr d.val = u ∧ tgt Gr d.val = v ∨ src Gr d.val = v ∧ tgt Gr d.val = u := by
  obtain ⟨p, hp⟩ := d
  simp

section noMultiEdgeGraphLike

variable {d : D} {Gr : Type*} {G : Gr}

/-- A graph-like structure with no multi-edge and symmetric darts. -/
class noMultiEdgeSymmGraphLike (V D E : outParam Type*) (Gr : Type*) extends
    SymmGraphLike V D E Gr, NoMultiEdgeGraphLike V D E Gr  where

@[simp]
theorem dartSym2_eq_iff [noMultiEdgeSymmGraphLike V D E Gr] (d₁ d₂ : darts G) :
    dartSym2 d₁ = dartSym2 d₂ ↔ d₁ = d₂ ∨ d₁ = dartSymm d₂ := by
  obtain ⟨p, hp⟩ := d₁
  obtain ⟨q, hq⟩ := d₂
  simp only [dartSym2_mk, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
    Subtype.mk.injEq, dartSymm_mk]
  refine ⟨?_, by rintro (rfl | rfl) <;> simp⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl <| dart_eq_of_src_tgt_eq h1 h2
  rw [← inv_src q] at h1
  rw [← inv_tgt q] at h2
  exact Or.inr <| dart_eq_of_src_tgt_eq h1 h2

end noMultiEdgeGraphLike
end GraphLike
