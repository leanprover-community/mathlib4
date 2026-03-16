/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sigma

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `HasDart` for capturing the common structure of different kinds of
graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HasDart`: is the main typeclass for capturing the common structure of graph-like structures.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `dart` gives the type of darts, which is an oriented edge, of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.
* A `prodDart` or half-edge or bond in a graph is an ordered pair of vertices with a `dart` between.
  It is regarded as an oriented edge.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.

-/

@[expose] public section

universe u'

/-- The `HasDart` typeclass abstracts over graph-like structures by encoding the minimal structure
required to reason about directed edges ("darts") and adjacency. This terminology comes from
combinatorial maps, and they are also known as "half-edges" or "bonds." `HasDart.{0}` can be used to
reason about graphs with `Prop`-valued darts. (`SimpleGraph` & `Digraph`) -/
class HasDart (α : outParam Type*) (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts (G : Gr) : Set α
  /-- The type of darts (oriented edges) of a graph-like structure. -/
  dart : Gr → α → α → Sort u'
  /-- The adjacency relation of a graph-like structure. -/
  Adj (G : Gr) (u v : α) : Prop := Nonempty (dart G u v)
  nonempty_dart_iff_adj {G : Gr} {u v : α} : Nonempty (dart G u v) ↔ Adj G u v := by rfl
  left_mem_verts_of_adj {G : Gr} {u v : α} (h : Adj G u v) : u ∈ verts G
  right_mem_verts_of_adj {G : Gr} {u v : α} (h : Adj G u v) : v ∈ verts G

namespace HasDart

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

section GeneralHasDart

variable {α Gr : Type*} [HasDart α Gr] {G : Gr} {v w : α}

/-- Dot notation for reverse direction of `adj_iff_nonempty_dart`. -/
lemma dart.adj (d : dart G v w) : Adj G v w := nonempty_dart_iff_adj.mp ⟨d⟩

/-- Dot notation for `left_mem_verts_of_adj`. -/
lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) :=
  left_mem_verts_of_adj h

/-- Dot notation for `right_mem_verts_of_adj`. -/
lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) :=
  right_mem_verts_of_adj h

lemma dart.left_mem (d : dart G v w) : v ∈ V(G) :=
  d.adj.left_mem

lemma dart.right_mem (d : dart G v w) : w ∈ V(G) :=
  d.adj.right_mem

/-- A `prodDart` is an oriented edge or A form of dart that does not have its end points in its
type. -/
structure prodDart [HasDart α Gr] (G : Gr) : Type (max u' u_1) extends α × α where
  /-- `fst` and `snd` have `dart` between them. -/
  dart' : (dart G fst snd : Sort u')

initialize_simps_projections prodDart (+toProd, -fst, -snd)

namespace prodDart

attribute [simp] dart'

lemma ext_iff (d₁ d₂ : prodDart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd ∧ d₁.dart' ≍ d₂.dart' := by
  cases d₁; cases d₂; simp

@[ext]
theorem ext (d₁ d₂ : prodDart G) (h : d₁.toProd = d₂.toProd) (h' : d₁.dart' ≍ d₂.dart') : d₁ = d₂ :=
  (ext_iff d₁ d₂).mpr ⟨h, h'⟩

end prodDart

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def prodDartAdj (G : Gr) (d d' : prodDart G) : Prop :=
  d.snd = d'.fst

end GeneralHasDart

section HasPDart

/-
### prodDart for `HasDart.{0} α Gr`

Some graph-like structures have `Prop`-valued darts, such as `SimpleGraph` and `Digraph` and there
exists a generality for such structures, separate from the general graph-like structures with
`HasDart` typeclass.

This section assumes `HasDart.{0} α Gr` to proves lemmas for `Prop`-valued darts.
-/

namespace prodDart

variable {α Gr : Type*} [HasDart.{0} α Gr] {G : Gr}

theorem ext_iff' (d₁ d₂ : prodDart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  simp +contextual only [ext_iff, and_iff_left_iff_imp, HEq.rfl, implies_true]

@[ext]
theorem ext' (d₁ d₂ : prodDart G) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (ext_iff' d₁ d₂).mpr h

theorem toProd_injective : Function.Injective (toProd : prodDart G → α × α) :=
  ext'

instance [DecidableEq α] (G : Gr) : DecidableEq (prodDart G) :=
  toProd_injective.decidableEq

instance fintype [Fintype α] [DecidableRel (dart G)] : Fintype (prodDart G) :=
  Fintype.ofEquiv (Σ v, { w | dart G v w })
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.dart'⟩ }

end prodDart
end HasPDart
end HasDart
