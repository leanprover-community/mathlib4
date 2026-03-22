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

@[expose] public section

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

section SymmGraphLike

variable [SymmDartLike α β] [SymmGraphLike α β Gr]

lemma inv_mem_darts (hd : d ∈ darts G) : inv α d ∈ darts G :=
  inv_mem_darts_iff.mpr hd

/-- The inverse of a step. -/
def step.inv (h : step G u v) : step G v u := ⟨SymmDartLike.inv α h.val, inv_mem_darts h.prop.1,
    (inv_fst.trans h.prop.2.2), inv_snd.trans h.prop.2.1⟩

@[simp]
lemma step.inv_val (h : step G u v) : h.inv.val = SymmDartLike.inv α h.val := by rfl

@[simp]
lemma step.inv_inv (h : step G u v) : h.inv.inv = h := by
  obtain ⟨d, hd, hu, hv⟩ := h
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

@[simp]
lemma step.todart_dartSym2 (h : step G u v) : dartSym2 h.todart = s(u, v) := by
  simp [dartSym2]

/-- The dart with reversed orientation from a given dart. -/
def dartSymm (d : darts G) : darts G := ⟨inv α d.val, inv_mem_darts_iff.mpr d.prop⟩

@[simp]
theorem dartSymm_mk {p : β} (h : p ∈ darts G) :
    dartSymm (⟨p, h⟩) = ⟨inv α p, inv_mem_darts_iff.mpr h⟩ :=
  rfl

@[simp]
lemma step.inv_todart (h : step G u v) : h.inv.todart = dartSymm h.todart := by
  simp [todart]

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

@[simp, grind =] lemma fst_eq : fst d = d.fst := rfl

@[simp, grind =] lemma snd_eq : snd d = d.snd := rfl

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

@[simp] lemma Adj.toStep_adj (h : Adj G u v) : (h.toStep).adj = h := rfl

@[simp]
lemma exists_step_iff_adj {P : (step G u v) → Prop} :
    (∃ s : step G u v, P s) ↔ (∃ h : Adj G u v, P (h.toStep)) := by
  refine ⟨fun ⟨s, hp⟩ ↦ ⟨s.adj, ?_⟩, fun ⟨h, hp⟩ ↦ ⟨h.toStep, hp⟩⟩
  rwa [Subsingleton.elim s.adj.toStep s]

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
