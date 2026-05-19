/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.PFun
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-! # Typeclass for graph-like data

- packaging junk values problematic due to non-defeq instances for the same type, move to relations
(more ergononmic than partially defined functions i think)
- method of undirected graph = directed modulo involution means the definition of trail (walk with
no duplicated edges) no longer works, bc the same edge could be traversed both ways.
-/

public section

open Prod Set

variable {V E Gr : Type*} {G : Gr} {e : E} {x y : V}

/-- The type `Gr` consists of graph-like objects on vertices `V` and edges `E`. Note that we
*cannot* require the converse of `isSource_left_of_isLink` and `isTarget_right_of_isLink` taken
together, as might be tempting: in an undirected graph we want, for instance `IsLink G e x y` and
`IsLink G e y x` to both be true, and this converse would then imply `IsLink G e x x`, which we
don't necessarily want. We also can't take `is{Source / Target}_{left / right}_of_isLink` as a
definition, to account for edges which have inputs but no outputs. -/
class HyperGraphLike (V E : outParam Type*) (Gr : Type*) where
  /-- The set of vertices of a graph. -/
  verts : Gr → Set V
  /-- The set of edges of a graph. -/
  edges : Gr → Set E
  /-- A vertex can acts as an input to an edge. -/
  IsSource : Gr → E → V → Prop
  /-- A vertex can acts as an output from an edge. -/
  IsTarget : Gr → E → V → Prop
  /-- An edges represents a walk of length one. -/
  IsLink : Gr → E → V → V → Prop
  mem_edges_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → e ∈ edges G
  mem_edges_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → e ∈ edges G
  mem_verts_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → x ∈ verts G
  mem_verts_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → x ∈ verts G
  isSource_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → IsSource G e x
  isTarget_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → IsTarget G e y

namespace HyperGraphLike

variable [HyperGraphLike V E Gr]

/-- Construct an instance based on source and target relations. `IsLink G e x y` is defined to be
`IsSource G e x ∧ IsTarget G e y`. -/
@[implicit_reducible]
def ofIsSourceIsTarget (verts : Gr → Set V) (edges : Gr → Set E)
    (IsSource : Gr → E → V → Prop) (IsTarget : Gr → E → V → Prop)
    (mem_edges_of_isSource : ∀ ⦃G e v⦄, IsSource G e v → e ∈ edges G)
    (mem_edges_of_isTarget : ∀ ⦃G e v⦄, IsTarget G e v → e ∈ edges G)
    (mem_verts_of_isSource : ∀ ⦃G e v⦄, IsSource G e v → v ∈ verts G)
    (mem_verts_of_isTarget : ∀ ⦃G e v⦄, IsTarget G e v → v ∈ verts G)
    : HyperGraphLike V E Gr where
  verts := verts
  edges := edges
  IsSource := IsSource
  IsTarget := IsTarget
  IsLink G e x y := IsSource G e x ∧ IsTarget G e y
  mem_edges_of_isSource := mem_edges_of_isSource
  mem_edges_of_isTarget := mem_edges_of_isTarget
  mem_verts_of_isSource := mem_verts_of_isSource
  mem_verts_of_isTarget := mem_verts_of_isTarget
  isSource_left_of_isLink _ _ _ _ h := h.1
  isTarget_right_of_isLink _ _ _ _ h := h.2

lemma IsSource.mem_verts (h : IsSource G e x) : x ∈ verts G := mem_verts_of_isSource h

lemma IsTarget.mem_verts (h : IsTarget G e x) : x ∈ verts G := mem_verts_of_isTarget h

lemma IsSource.mem_edges (h : IsSource G e x) : e ∈ edges G := mem_edges_of_isSource h

lemma IsTarget.mem_edges (h : IsTarget G e x) : e ∈ edges G := mem_edges_of_isTarget h

lemma IsLink.isSource_left (h : IsLink G e x y) : IsSource G e x := isSource_left_of_isLink h

lemma IsLink.isTarget_right (h : IsLink G e x y) : IsTarget G e y := isTarget_right_of_isLink h

lemma IsLink.mem_verts_left (h : IsLink G e x y) : x ∈ verts G := h.isSource_left.mem_verts

lemma IsLink.mem_verts_right (h : IsLink G e x y) : y ∈ verts G := h.isTarget_right.mem_verts

lemma IsLink.mem_edges (h : IsLink G e x y) : e ∈ edges G := h.isSource_left.mem_edges

/-- Notion of adjacency derived from `IsLink`. -/
def Adj (G : Gr) (x y : V) : Prop := ∃ e, IsLink G e x y

lemma Adj.mem_verts_left (h : Adj G x y) : x ∈ verts G :=
  have ⟨_, h⟩ := h
  h.mem_verts_left

lemma Adj.mem_verts_right (h : Adj G x y) : y ∈ verts G :=
  have ⟨_, h⟩ := h
  h.mem_verts_right

/-- A `Dart` is a walk of length one. -/
structure Dart (G : Gr) where
  src : V
  tgt : V
  edge : E
  h : IsLink G edge src tgt

namespace Dart

@[ext]
protected lemma ext {d d' : Dart G} (hs : d.src = d'.src) (ht : d.tgt = d'.tgt)
    (he : d.edge = d'.edge) : d = d' := by
  cases d; cases d'; congr

lemma src_mem (d : Dart G) : d.src ∈ verts G := d.h.mem_verts_left

lemma tgt_mem (d : Dart G) : d.tgt ∈ verts G := d.h.mem_verts_right

lemma edge_mem (d : Dart G) : d.edge ∈ edges G := d.h.mem_edges

lemma adj (d : Dart G) : Adj G d.src d.tgt := ⟨d.edge, d.h⟩

/-- Darts are adjacent if they can appear as consecutive steps in a walk. -/
def AdjDart (d d' : Dart G) : Prop := d.tgt = d'.src

end Dart

/-- This is weaker than requiring that the clauses listed *determine* the order relation,
but it ought to be enough to define eg lifting walks from a subgraph. -/
class HyperGraphLikeLE (Gr : Type*) [HyperGraphLike V E Gr] [LE Gr] where
  verts_mono {H G : Gr} : H ≤ G → verts H ⊆ verts G
  edges_mono {H G : Gr} : H ≤ G → edges H ⊆ edges G
  isSource_mono {H G : Gr} : H ≤ G → ∀ ⦃e x⦄, IsSource H e x → IsSource G e x
  isTarget_mono {H G : Gr} : H ≤ G → ∀ ⦃e y⦄, IsTarget H e y → IsTarget G e y
  isLink_mono {H G : Gr} : H ≤ G → ∀ ⦃e x y⦄, IsLink H e x y → IsLink G e x y

end HyperGraphLike

open HyperGraphLike

/-- A class for hypergraphs with no orientation on edges, so that `IsSource` and `IsTarget` agree
and `IsLink` is symmetric. -/
class HyperGraphLike.Symm (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike V E Gr where
  isSource_iff_isTarget : ∀ ⦃G e x⦄, IsSource G e x ↔ IsTarget G e x
  isLink_symm : ∀ ⦃G e⦄, Symmetric (IsLink G e)

namespace HyperGraphLike.Symm

variable [HyperGraphLike.Symm V E Gr]

lemma adj_symm : Symmetric (Adj G) := by
  intro x y ⟨e, h⟩
  exact ⟨e, isLink_symm h⟩

-- etc API lemmas as for `Graph`

end HyperGraphLike.Symm

/-- A `GraphLike` type, where each edge connects a unique (not necessarily distinct) pair
of vertices. For this class and those inheriting it, `IsSource` and `IsTarget` are inferred from
`IsLink`. -/
class GraphLike (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike V E Gr where
  mem_edges_iff_exists_isLink : ∀ ⦃G e⦄, e ∈ edges G ↔ ∃ x y, IsLink G e x y
  isSource_iff_exists_isLink : ∀ ⦃G e x⦄, IsSource G e x ↔ ∃ y, IsLink G e x y
  isTarget_iff_exists_isLink : ∀ ⦃G e y⦄, IsTarget G e y ↔ ∃ x, IsLink G e x y
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink : ∀ ⦃G : Gr⦄ ⦃e x y x' y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y' ∨ x = y' ∧ y = x'

namespace GraphLike

/-- Construct a `GraphLike` instance directly from the `IsLink` relation. `IsSource` and `IsTarget`
are given their only possible definitions. -/
@[implicit_reducible]
def ofIsLink (verts : Gr → Set V) (IsLink : Gr → E → V → V → Prop)
    (mem_verts_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → x ∈ verts G)
    (mem_verts_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → y ∈ verts G)
    (eq_and_eq_or_eq_and_eq_of_isLink_of_isLink : ∀ ⦃G e x y x' y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y' ∨ x = y' ∧ y = x') :
    GraphLike V E Gr where
  verts := verts
  edges G := {e | ∃ x y, IsLink G e x y}
  IsSource G e x := ∃ y, IsLink G e x y
  IsTarget G e y := ∃ x, IsLink G e x y
  IsLink := IsLink
  mem_edges_of_isSource _ _ x h := ⟨x, h⟩
  mem_edges_of_isTarget _ _ y := fun ⟨x, h⟩ => ⟨x, y, h⟩
  mem_verts_of_isSource _ _ _ := fun ⟨_, h⟩ => mem_verts_left_of_isLink h
  mem_verts_of_isTarget _ _ _ := fun ⟨_, h⟩ => mem_verts_right_of_isLink h
  mem_edges_iff_exists_isLink _ _ := Iff.rfl
  isSource_iff_exists_isLink _ _ _ := Iff.rfl
  isTarget_iff_exists_isLink _ _ _ := Iff.rfl
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink := eq_and_eq_or_eq_and_eq_of_isLink_of_isLink
  isSource_left_of_isLink _ _ _ y h := ⟨y, h⟩
  isTarget_right_of_isLink _ _ x _ h := ⟨x, h⟩

/-- A simple `GraphLike` type has at most one edge linking any two vertices. -/
class Simple (V E : outParam Type*) (Gr : Type*) extends GraphLike V E Gr where
  eq_of_isLink_of_isLink : ∀ ⦃G e e' x y⦄, IsLink G e x y → IsLink G e' x y → e = e'

variable [GraphLike V E Gr]

noncomputable def endpoints (he : e ∈ edges G) : Sym2 V :=
  s(Classical.choose (mem_edges_iff_exists_isLink.mp he),
    Classical.choose <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp he))

lemma eq_endpoints_of_isLink (h : IsLink G e x y) : s(x, y) = endpoints h.mem_edges := by
  simpa [endpoints] using eq_and_eq_or_eq_and_eq_of_isLink_of_isLink (G := G) (e := e) h <|
    Classical.choose_spec <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp h.mem_edges)

/-- A convenient constructor for `HyperGraphLikeLE` in the case of graphlike types. -/
@[implicit_reducible]
def hyperGraphLikeLE [LE Gr] (hverts : ∀ {H G : Gr}, H ≤ G → verts H ⊆ verts G)
    (hedges : ∀ {H G : Gr}, H ≤ G → edges H ⊆ edges G)
    (hlink : ∀ {H G : Gr}, H ≤ G → ∀ ⦃e x y⦄, IsLink H e x y → IsLink G e x y) :
    HyperGraphLikeLE Gr where
  verts_mono := hverts
  edges_mono := hedges
  isSource_mono h e x := by grind [isSource_iff_exists_isLink]
  isTarget_mono h e x := by grind [isTarget_iff_exists_isLink]
  isLink_mono := hlink

end GraphLike

open GraphLike

/-- In a `DigraphLike` type, each edge has a unique source and target. -/
class DigraphLike (V E : outParam Type*) (Gr : Type*) extends
    GraphLike V E Gr where
  eq_of_isSource_of_isSource : ∀ ⦃G e x x'⦄, IsSource G e x → IsSource G e x' → x = x'
  eq_of_isTarget_of_isTarget : ∀ ⦃G e y y'⦄, IsTarget G e y → IsTarget G e y' → y = y'

namespace DigraphLike

@[implicit_reducible]
def ofSourceTarget (verts : Gr → Set V) (edges : Gr → Set E) (src : Gr → E → V)
    (tgt : Gr → E → V) (mem_verts_src : ∀ ⦃G e⦄, e ∈ edges G → src G e ∈ verts G)
    (mem_verts_tgt : ∀ ⦃G e⦄, e ∈ edges G → tgt G e ∈ verts G) : DigraphLike V E Gr where
  verts := verts
  edges := edges
  IsSource G e x := e ∈ edges G ∧ src G e = x
  IsTarget G e y := e ∈ edges G ∧ tgt G e = y
  IsLink G e x y := e ∈ edges G ∧ src G e = x ∧ tgt G e = y
  mem_edges_of_isSource _ _ _ h := h.1
  mem_edges_of_isTarget _ _ _ h := h.1
  mem_verts_of_isSource _ _ _ := fun ⟨he, hx⟩ => hx ▸ mem_verts_src he
  mem_verts_of_isTarget _ _ _ := fun ⟨he, hy⟩ => hy ▸ mem_verts_tgt he
  isSource_left_of_isLink _ _ _ _ := fun ⟨he, hx, _⟩ => ⟨he, hx⟩
  isTarget_right_of_isLink _ _ _ _ := fun ⟨he, _, hy⟩ => ⟨he, hy⟩
  mem_edges_iff_exists_isLink G e :=
      ⟨fun he => ⟨src G e, tgt G e, he, rfl, rfl⟩, fun ⟨_, _, he, _, _⟩ => he⟩
  isSource_iff_exists_isLink G e _ :=
      ⟨fun ⟨he, hx⟩ => ⟨tgt G e, he, hx, rfl⟩, fun ⟨_, he, hx, _⟩ => ⟨he, hx⟩⟩
  isTarget_iff_exists_isLink G e _ :=
      ⟨fun ⟨he, hy⟩ => ⟨src G e, he, rfl, hy⟩, fun ⟨_, he, _, hy⟩ => ⟨he, hy⟩⟩
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink _ _ _ _ _ _ :=
      fun ⟨_, hx, hy⟩ ⟨_, hx', hy'⟩ => Or.inl ⟨hx.symm.trans hx', hy.symm.trans hy'⟩
  eq_of_isSource_of_isSource _ _ _ _ := fun ⟨_, hx⟩ ⟨_, hx'⟩ => hx.symm.trans hx'
  eq_of_isTarget_of_isTarget _ _ _ _ := fun ⟨_, hy⟩ ⟨_, hy'⟩ => hy.symm.trans hy'

variable [DigraphLike V E Gr]

noncomputable def src (he : e ∈ edges G) : V :=
    Classical.choose (mem_edges_iff_exists_isLink.mp he)

noncomputable def tgt (he : e ∈ edges G) : V :=
    Classical.choose <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp he)

lemma isLink_src_tgt (he : e ∈ edges G) : IsLink G e (src he) (tgt he) :=
    Classical.choose_spec <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp he)

lemma isSource_src (he : e ∈ edges G) : IsSource G e (src he) := isLink_src_tgt he |>.isSource_left

lemma isTarget_tgt (he : e ∈ edges G) : IsTarget G e (tgt he) := isLink_src_tgt he |>.isTarget_right

lemma eq_src_left_of_isLink (h : IsLink G e x y) : x = src h.mem_edges :=
  eq_of_isSource_of_isSource h.isSource_left (isSource_src h.mem_edges)

lemma eq_tgt_right_of_isLink (h : IsLink G e x y) : y = tgt h.mem_edges :=
  eq_of_isTarget_of_isTarget h.isTarget_right (isTarget_tgt h.mem_edges)

lemma isLink_iff_eq_src_eq_tgt (he : e ∈ edges G) (x y : V) :
    IsLink G e x y ↔ x = src he ∧ y = tgt he :=
  ⟨fun h => ⟨eq_src_left_of_isLink h, eq_tgt_right_of_isLink h⟩,
    fun ⟨hx, hy⟩ => hx ▸ hy ▸ isLink_src_tgt he⟩

lemma eq_and_eq_of_isLink_of_isLink {e : E} {x y x' y' : V} (h : IsLink G e x y)
    (h' : IsLink G e x' y') : x = x' ∧ y = y' :=
  ⟨eq_of_isSource_of_isSource h.isSource_left h'.isSource_left,
  eq_of_isTarget_of_isTarget h.isTarget_right h'.isTarget_right⟩

end DigraphLike

open DigraphLike

/-- In an irreflexive hypergraph-like type, there is no length-one walk from a vertex to itself. -/
class IrreflHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  not_isLink_self_self : ∀ ⦃G e x⦄, ¬ (IsLink G e x x)

/-- `Digraph` is indeed `DigraphLike`... -/
instance instDigraphLikeDigraph : DigraphLike V (V × V) (Digraph V) :=
  ofSourceTarget (Gr := Digraph V)
  (verts := fun _ => Set.univ) (edges := fun G => {p : V × V | G.Adj p.1 p.2})
  (src := fun _ => Prod.fst) (tgt := fun _ => Prod.snd)
  (mem_verts_src := fun _ _ _ => trivial) (mem_verts_tgt := fun _ _ _ => trivial)

/-- ... and simple. -/
instance : GraphLike.Simple V (V × V) (Digraph V) where
  eq_of_isLink_of_isLink G e e' x y h h' := by
    cases e; cases e'
    simp_all [IsLink]

/-- `Graph` is `GraphLike` ... -/
instance : GraphLike V E (Graph V E) := by
  refine ofIsLink Graph.vertexSet Graph.IsLink ?_ ?_ ?_
  · intro G e x y h
    exact h.left_mem
  · intro G e x y h
    exact h.right_mem
  · intro G e x y x' y' h h'
    exact h.eq_and_eq_or_eq_and_eq h'

/-- ... and symmetric. -/
instance : HyperGraphLike.Symm V E (Graph V E) where
  isSource_iff_isTarget G e x := by
    simp [IsSource, IsTarget]
    grind [Graph.isLink_comm]
  isLink_symm G e := by
    intro x y h
    exact h.symm

-- sanity check
lemma Graph.edges_eq_edgeSet (G : Graph V E) : edges G = G.edgeSet := by
  ext x
  simp [edges, G.edge_mem_iff_exists_isLink]

instance : HyperGraphLikeLE (Graph V E) := by
  refine GraphLike.hyperGraphLikeLE ?_ ?_ ?_
  · intro _ _ h; exact h.vertexSet_mono
  · intro _ _ h; simpa [Graph.edges_eq_edgeSet] using h.edgeSet_mono
  · intro _ _ h; exact h.isLink_mono

/-- `SimpleGraph` is `Graphlike`, ... -/
instance : GraphLike V (Sym2 V) (SimpleGraph V) := by
  refine ofIsLink (fun _ => Set.univ) (fun (G : SimpleGraph V) e x y => G.Adj x y ∧ e = s(x, y))
    ?_ ?_ ?_
  · intro G e x y h; trivial
  · intro G e x y h; trivial
  · rintro G e x y x' y' ⟨_, rfl⟩ ⟨_, h⟩
    grind

/-- ... symmetric, ... -/
instance : HyperGraphLike.Symm V (Sym2 V) (SimpleGraph V) where
  isSource_iff_isTarget G e x := by
    simp [IsSource, IsTarget]
    grind [G.adj_comm]
  isLink_symm G e h := by
    simp [IsLink]
    grind [G.adj_comm]

/-- ... simple, ... -/
instance : GraphLike.Simple V (Sym2 V) (SimpleGraph V) where
  eq_of_isLink_of_isLink G e e' x y := by rintro ⟨h, rfl⟩ ⟨h', rfl⟩; rfl

/-- ... and irreflexive. -/
instance : IrreflHyperGraphLike V (Sym2 V) (SimpleGraph V) where
  not_isLink_self_self G e x := by simp [IsLink]

-- sanity checks.
lemma SimpleGraph.edges_eq_edgeSet (G : SimpleGraph V) : edges G = G.edgeSet := by
  ext x
  rcases x with ⟨x, y⟩
  simp [edges]
  grind [G.adj_comm]

lemma SimpleGraph.adj_iff_adj (G : SimpleGraph V) (x y : V) :
    G.Adj x y ↔ HyperGraphLike.Adj G x y := by
  simp [HyperGraphLike.Adj, IsLink]

def SimpleGraph.dart_equiv_dart (G : SimpleGraph V) :
    G.Dart ≃ HyperGraphLike.Dart G where
  toFun d := ⟨d.fst, d.snd, s(d.fst, d.snd), d.adj, rfl⟩
  invFun d := ⟨⟨d.src, d.tgt⟩, (G.adj_iff_adj _ _).mpr d.adj⟩
  right_inv d := by rcases d with ⟨x, y, e, h, rfl⟩; simp

section HalfEdge

/-! A rough definition and instance(s) to show that a graph-like type defined in terms of half-edges
can be fit (faithfully imo) into this framework. -/

structure BondGraph (V E : Type*) where
  verts : Set V
  edges : Set E
  endpoint : E → V
  endpoint_mem_of_mem : ∀ ⦃e⦄, e ∈ edges → endpoint e ∈ verts
  swap : E → E
  swap_mem_of_mem : ∀ ⦃e⦄, e ∈ edges → swap e ∈ edges
  swap_swap_eq_of_mem : ∀ ⦃e⦄, e ∈ edges → swap (swap e) = e

instance : GraphLike V (Sym2 E) (BondGraph V E) where
  verts G := G.verts
  edges G := {s(e, G.swap e) | e ∈ G.edges}
  IsSource G e x := ∃ f ∈ G.edges, G.endpoint f = x ∧ s(f, G.swap f) = e
  IsTarget G e x := ∃ f ∈ G.edges, G.endpoint f = x ∧ s(f, G.swap f) = e
  IsLink G e x y := ∃ f ∈ G.edges, G.endpoint f = x ∧ G.endpoint (G.swap f) = y ∧ s(f, G.swap f) = e
  mem_edges_of_isSource G e x := by rintro ⟨f, hf, _, rfl⟩; use f
  mem_edges_of_isTarget G e y := by rintro ⟨f, hf, _, rfl⟩; use f
  mem_verts_of_isSource G e x := by rintro ⟨f, hf, rfl, _⟩; exact G.endpoint_mem_of_mem hf
  mem_verts_of_isTarget G e x := by rintro ⟨f, hf, rfl, _⟩; exact G.endpoint_mem_of_mem hf
  isSource_left_of_isLink G e x y := by rintro ⟨f, hf, rfl, rfl, rfl⟩; use f
  isTarget_right_of_isLink G e x y := by
    rintro ⟨f, hf, rfl, rfl, rfl⟩
    use G.swap f, G.swap_mem_of_mem hf, rfl
    rw [Sym2.eq_swap, G.swap_swap_eq_of_mem hf]
  mem_edges_iff_exists_isLink G e := by simp
  isSource_iff_exists_isLink G e x := by simp
  isTarget_iff_exists_isLink G e y := by
    constructor
    · rintro ⟨f, hf, rfl, rfl⟩
      use G.endpoint (G.swap f), G.swap f, G.swap_mem_of_mem hf, rfl
      simp [G.swap_swap_eq_of_mem hf]
    · rintro ⟨x, f, hf, rfl, rfl, rfl⟩
      use G.swap f, G.swap_mem_of_mem hf, rfl
      simp [G.swap_swap_eq_of_mem hf]
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink G _ _ _ _ _ := by
    simp only [forall_exists_index, and_imp]
    rintro e he rfl rfl rfl f hf rfl rfl
    simp only [Sym2.eq, Sym2.rel_iff', mk.injEq, swap_prod_mk]
    rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · simp
    · simp [G.swap_swap_eq_of_mem he]

structure IrreflBondGraph (V E : Type*) extends BondGraph V E where
  endpoint_ne_endpoint_swap : ∀ ⦃e⦄, e ∈ edges → endpoint e ≠ endpoint (swap e)
  -- ne_swap_self : ∀ ⦃e⦄, e ∈ edges → swap e ≠ e

instance : GraphLike V (Sym2 E) (IrreflBondGraph V E) where
  verts G := G.verts
  edges G := {s(e, G.swap e) | e ∈ G.edges}
  IsSource G e x := ∃ f ∈ G.edges, G.endpoint f = x ∧ s(f, G.swap f) = e
  IsTarget G e x := ∃ f ∈ G.edges, G.endpoint f = x ∧ s(f, G.swap f) = e
  IsLink G e x y := ∃ f ∈ G.edges, G.endpoint f = x ∧ G.endpoint (G.swap f) = y ∧ s(f, G.swap f) = e
  mem_edges_of_isSource G e x := by rintro ⟨f, hf, _, rfl⟩; use f
  mem_edges_of_isTarget G e y := by rintro ⟨f, hf, _, rfl⟩; use f
  mem_verts_of_isSource G e x := by rintro ⟨f, hf, rfl, _⟩; exact G.endpoint_mem_of_mem hf
  mem_verts_of_isTarget G e x := by rintro ⟨f, hf, rfl, _⟩; exact G.endpoint_mem_of_mem hf
  isSource_left_of_isLink G e x y := by rintro ⟨f, hf, rfl, rfl, rfl⟩; use f
  isTarget_right_of_isLink G e x y := by
    rintro ⟨f, hf, rfl, rfl, rfl⟩
    use G.swap f, G.swap_mem_of_mem hf, rfl
    rw [Sym2.eq_swap, G.swap_swap_eq_of_mem hf]
  mem_edges_iff_exists_isLink G e := by simp
  isSource_iff_exists_isLink G e x := by simp
  isTarget_iff_exists_isLink G e y := by
    constructor
    · rintro ⟨f, hf, rfl, rfl⟩
      use G.endpoint (G.swap f), G.swap f, G.swap_mem_of_mem hf, rfl
      simp [G.swap_swap_eq_of_mem hf]
    · rintro ⟨x, f, hf, rfl, rfl, rfl⟩
      use G.swap f, G.swap_mem_of_mem hf, rfl
      simp [G.swap_swap_eq_of_mem hf]
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink G _ _ _ _ _ := by
    simp only [forall_exists_index, and_imp]
    rintro e he rfl rfl rfl f hf rfl rfl
    simp only [Sym2.eq, Sym2.rel_iff', mk.injEq, swap_prod_mk]
    rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · simp
    · simp [G.swap_swap_eq_of_mem he]

instance : IrreflHyperGraphLike V (Sym2 E) (IrreflBondGraph V E) where
  not_isLink_self_self G e x := by
    rintro ⟨f, hf, rfl, h, _⟩
    exact G.endpoint_ne_endpoint_swap hf h.symm

end HalfEdge

-- i don't think this is particularly interesting but it is at least possible
instance : HyperGraphLike V (Finset V) (AbstractSimplicialComplex V) := by
  refine ofIsSourceIsTarget (fun _ => Set.univ) (fun K => K.faces) (fun K e x => e ∈ K ∧ x ∈ e)
      (fun K e x => e ∈ K ∧ x ∈ e) (fun _ _ _ h => h.1) (fun _ _ _ h => h.1)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
