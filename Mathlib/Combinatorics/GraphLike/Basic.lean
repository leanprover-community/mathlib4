/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.PFun
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-! # Typeclass for graph-like data

- packaging junk values problematic due to non-defeq instances for the same type, move to relations
(more ergononmic than partially defined functions i think)
- method of undirected graph = directed modulo involution means the definition of trail (walk with
no duplicated edges) no longer works, bc the same edge could be traversed both ways.
-/

public section

open Prod Set

variable {V E Gr : Type*} {G : Gr} {e : E} {x y : V}

class HyperGraphLike (V E : outParam Type*) (Gr : Type*) where
  verts : Gr → Set V
  edges : Gr → Set E
  IsSource : Gr → E → V → Prop
  IsTarget : Gr → E → V → Prop
  IsLink : Gr → E → V → V → Prop
  mem_edges_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → e ∈ edges G
  mem_edges_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → e ∈ edges G
  mem_verts_of_isSource : ∀ ⦃G e x⦄, IsSource G e x → x ∈ verts G
  mem_verts_of_isTarget : ∀ ⦃G e x⦄, IsTarget G e x → x ∈ verts G
  isSource_left_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → IsSource G e x
  isTarget_right_of_isLink : ∀ ⦃G e x y⦄, IsLink G e x y → IsTarget G e y

namespace HyperGraphLike

variable [instHGL : HyperGraphLike V E Gr]

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

def Adj (G : Gr) (x y : V) : Prop := ∃ e, IsLink G e x y

lemma Adj.mem_verts_left (h : Adj G x y) : x ∈ verts G :=
  have ⟨_, h⟩ := h
  h.mem_verts_left

lemma Adj.mem_verts_right (h : Adj G x y) : y ∈ verts G :=
  have ⟨_, h⟩ := h
  h.mem_verts_right

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

def AdjDart (d d' : Dart G) : Prop := d.tgt = d'.src

end Dart

end HyperGraphLike

open HyperGraphLike

class HyperGraphLike.Symm (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike V E Gr where
  isSource_iff_isTarget : ∀ ⦃G e x⦄, IsSource G e x ↔ IsTarget G e x
  isLink_symm : ∀ ⦃G e⦄, Symmetric (IsLink G e)

namespace HyperGraphLike.Symm

variable [HyperGraphLike.Symm V E Gr]

lemma adj_symm : Symmetric (Adj G) := by
  intro x y ⟨e, h⟩
  exact ⟨e, isLink_symm h⟩

-- -- etc API lemmas as for `Graph`

end HyperGraphLike.Symm

class GraphLike (V E : outParam Type*) (Gr : Type*) extends HyperGraphLike V E Gr where
  mem_edges_iff_exists_isLink : ∀ ⦃G e⦄, e ∈ edges G ↔ ∃ x y, IsLink G e x y
  isSource_iff_exists_isLink : ∀ ⦃G e x⦄, IsSource G e x ↔ ∃ y, IsLink G e x y
  isTarget_iff_exists_isLink : ∀ ⦃G e y⦄, IsTarget G e y ↔ ∃ x, IsLink G e x y
  eq_and_eq_or_eq_and_eq_of_isLink_of_isLink : ∀ ⦃G : Gr⦄ ⦃e x y x' y'⦄,
      IsLink G e x y → IsLink G e x' y' → x = x' ∧ y = y' ∨ x = y' ∧ y = x'

namespace DirGraphLike

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

class Simple (V E : outParam Type*) (Gr : Type*) extends GraphLike V E Gr where
  eq_of_isLink_of_isLink : ∀ ⦃G e e' x y⦄, IsLink G e x y → IsLink G e' x y → e = e'

class Directed (V E : outParam Type*) (Gr : Type*) extends GraphLike V E Gr where
  existsUnique_isLink_of_mem_edges : ∀ ⦃G e⦄, e ∈ edges G → ∃! x, ∃! y, IsLink G e x y

variable [GraphLike V E Gr]

noncomputable def endpoints (he : e ∈ edges G) : Sym2 V :=
  s(Classical.choose (mem_edges_iff_exists_isLink.mp he),
    Classical.choose <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp he))

lemma eq_endpoints_of_isLink (h : IsLink G e x y) : s(x, y) = endpoints h.mem_edges := by
  simpa [endpoints] using eq_and_eq_or_eq_and_eq_of_isLink_of_isLink (G := G) (e := e) h <|
    Classical.choose_spec <| Classical.choose_spec (mem_edges_iff_exists_isLink.mp h.mem_edges)

end DirGraphLike

open DirGraphLike

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

end DigraphLike

open DigraphLike

class IrreflHyperGraphLike (V E : outParam Type*) (Gr : Type*) extends
    HyperGraphLike V E Gr where
  not_isLink_self_self : ∀ ⦃G e x⦄, ¬ (IsLink G e x x)

instance instDigraphLikeDigraph : DigraphLike V (V × V) (Digraph V) :=
  ofSourceTarget (Gr := Digraph V)
  (verts := fun _ => Set.univ) (edges := fun G => {p : V × V | G.Adj p.1 p.2})
  (src := fun _ => Prod.fst) (tgt := fun _ => Prod.snd)
  (mem_verts_src := fun _ _ _ => trivial) (mem_verts_tgt := fun _ _ _ => trivial)

instance : GraphLike.Simple V (V × V) (Digraph V) where
  eq_of_isLink_of_isLink G e e' x y h h' := by
    cases e; cases e'
    simp_all [IsLink]

instance : GraphLike V E (Graph V E) := by
  refine ofIsLink Graph.vertexSet Graph.IsLink ?_ ?_ ?_
  · intro G e x y h
    exact h.left_mem
  · intro G e x y h
    exact h.right_mem
  · intro G e x y x' y' h h'
    exact h.eq_and_eq_or_eq_and_eq h'

-- sanity check
lemma Graph.edges_eq_edgeSet (G : Graph V E) : edges G = G.edgeSet := by
  ext x
  simp [edges, G.edge_mem_iff_exists_isLink]

instance : HyperGraphLike.Symm V E (Graph V E) where
  isSource_iff_isTarget G e x := by
    simp [IsSource, IsTarget]
    grind [Graph.isLink_comm]
  isLink_symm G e := by
    intro x y h
    exact h.symm

instance : GraphLike V (Sym2 V) (SimpleGraph V) := by
  refine ofIsLink (fun _ => Set.univ) (fun (G : SimpleGraph V) e x y => G.Adj x y ∧ e = s(x, y))
    ?_ ?_ ?_
  · intro G e x y h; trivial
  · intro G e x y h; trivial
  · rintro G e x y x' y' ⟨_, rfl⟩ ⟨_, h⟩
    grind

instance : HyperGraphLike.Symm V (Sym2 V) (SimpleGraph V) where
  isSource_iff_isTarget G e x := by
    simp [IsSource, IsTarget]
    grind [G.adj_comm]
  isLink_symm G e h := by
    simp [IsLink]
    grind [G.adj_comm]

instance : IrreflHyperGraphLike V (Sym2 V) (SimpleGraph V) where
  not_isLink_self_self G e x := by simp [IsLink]

section HalfEdge

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
