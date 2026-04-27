/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Fintype.Powerset

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `Subgraph G` is the type of subgraphs of a `G : SimpleGraph V`.

* `Subgraph.neighborSet`, `Subgraph.incidenceSet`, and `Subgraph.degree` are like their
  `SimpleGraph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `Subgraph.coe` is the coercion from a `G' : Subgraph G` to a `SimpleGraph G'.verts`.
  (In Lean 3 this could not be a `Coe` instance since the destination type depends on `G'`.)

* `Subgraph.IsSpanning` for whether a subgraph is a spanning subgraph and
  `Subgraph.IsInduced` for whether a subgraph is an induced subgraph.

* Instances for `Lattice (Subgraph G)` and `BoundedOrder (Subgraph G)`.

* `SimpleGraph.toSubgraph`: If a `SimpleGraph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `SimpleGraph.Subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`Subgraph.map_top`) and between subgraphs
  (`Subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `SetLike` does not apply to
  this kind of subobject.

## TODO

* Images of graph homomorphisms as subgraphs.

-/

@[expose] public section


universe u v

namespace SimpleGraph

/-- A subgraph of a `SimpleGraph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `Set (V × V)`, a set of darts (i.e., half-edges), then
`Subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure Subgraph {V : Type u} (G : SimpleGraph V) where
  /-- Vertices of the subgraph -/
  verts : Set V
  /-- Edges of the subgraph -/
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, Adj v w → G.Adj v w
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Symmetric Adj := by aesop_graph

initialize_simps_projections SimpleGraph.Subgraph (Adj → adj)

variable {ι : Sort*} {V : Type u} {W : Type v}

/-- The one-vertex subgraph. -/
@[simps]
protected def singletonSubgraph (G : SimpleGraph V) (v : V) : G.Subgraph where
  verts := {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert := False.elim
  symm _ _ := False.elim

/-- The one-edge subgraph. -/
@[simps]
def subgraphOfAdj (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) : G.Subgraph where
  verts := {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet, ← h]
    exact hvw
  edge_vert {a b} h := by
    apply_fun fun e ↦ a ∈ e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h

namespace Subgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.Subgraph} {a b : V}

protected theorem loopless (G' : Subgraph G) : Std.Irrefl G'.Adj :=
  ⟨fun v h ↦ G.loopless.irrefl v (G'.adj_sub h)⟩

theorem adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  ⟨fun x ↦ G'.symm x, fun x ↦ G'.symm x⟩

@[symm]
theorem adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h

protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  h.symm.fst_mem

protected theorem Adj.ne {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ≠ v :=
  h.adj_sub.ne

theorem adj_congr_of_sym2 {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x)) :
    H.Adj u v ↔ H.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

/-- Coercion from `G' : Subgraph G` to a `SimpleGraph G'.verts`. -/
@[simps]
protected def coe (G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm _ _ h := G'.symm h
  loopless := ⟨fun v h ↦ loopless G |>.irrefl v (G'.adj_sub h)⟩

@[simp]
theorem Adj.adj_sub' (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v) : G.Adj u v :=
  G'.adj_sub h

theorem coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

-- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
protected theorem Adj.coe {H : G.Subgraph} {u v : V} (h : H.Adj u v) :
    H.coe.Adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert h.symm⟩ := h

instance (G : SimpleGraph V) (H : Subgraph G) [DecidableRel H.Adj] : DecidableRel H.coe.Adj :=
  fun a b ↦ ‹DecidableRel H.Adj› _ _

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (G' : Subgraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts

theorem isSpanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

/-- Coercion from `Subgraph G` to `SimpleGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (G' : Subgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless := ⟨fun v hv ↦ G.loopless.irrefl v (G'.adj_sub hv)⟩

@[simp]
lemma spanningCoe_coe (G' : G.Subgraph) : G'.coe.spanningCoe = G'.spanningCoe := by
  ext
  simp only [map_adj, Function.Embedding.subtype_apply, Subtype.exists]
  grind [spanningCoe_adj, coe_adj, edge_vert, adj_symm]

theorem Adj.of_spanningCoe {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v) :
    G.Adj u v :=
  G'.adj_sub h

lemma spanningCoe_le (G' : G.Subgraph) : G'.spanningCoe ≤ G := fun _ _ ↦ G'.3

theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  simp [Subgraph.spanningCoe]

lemma mem_of_adj_spanningCoe {v w : V} {s : Set V} (G : SimpleGraph s)
    (hadj : G.spanningCoe.Adj v w) : v ∈ s := by aesop

@[simp]
lemma spanningCoe_subgraphOfAdj {v w : V} (hadj : G.Adj v w) :
    (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

/-- `coe` can be embedded in `spanningCoe`. -/
@[simps]
def coeEmbeddingSpanningCoe (G' : Subgraph G) : G'.coe ↪g G'.spanningCoe where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := .rfl

/-- `spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`. -/
@[simps]
def spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) :
    G'.spanningCoe ≃g G'.coe where
  toFun v := ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def IsInduced (G' : Subgraph G) : Prop :=
  ∀ ⦃v⦄, v ∈ G'.verts → ∀ ⦃w⦄, w ∈ G'.verts → G.Adj v w → G'.Adj v w

@[simp] protected lemma IsInduced.adj {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (H : Subgraph G) : Set V := SetRel.dom {(v, w) | H.Adj v w}

theorem mem_support (H : Subgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.Adj v w := Iff.rfl

theorem support_subset_verts (H : Subgraph G) : H.support ⊆ H.verts :=
  fun _ ⟨_, h⟩ ↦ H.edge_vert h

/-- `G'.neighborSet v` is the set of vertices adjacent to `v` in `G'`. -/
def neighborSet (G' : Subgraph G) (v : V) : Set V := {w | G'.Adj v w}

theorem neighborSet_subset (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G.neighborSet v :=
  fun _ ↦ G'.adj_sub

theorem neighborSet_subset_verts (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G'.verts :=
  fun _ h ↦ G'.edge_vert (adj_symm G' h)

@[simp]
theorem mem_neighborSet (G' : Subgraph G) (v w : V) : w ∈ G'.neighborSet v ↔ G'.Adj v w := Iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coeNeighborSetEquiv {G' : Subgraph G} (v : G'.verts) :
    G'.coe.neighborSet v ≃ G'.neighborSet v where
  toFun w := ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edgeSet (G' : Subgraph G) : Set (Sym2 V) := Sym2.fromRel G'.symm

theorem edgeSet_subset (G' : Subgraph G) : G'.edgeSet ⊆ G.edgeSet :=
  Sym2.ind (fun _ _ ↦ G'.adj_sub)

@[simp]
protected lemma mem_edgeSet {G' : Subgraph G} {v w : V} : s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w := .rfl

@[simp] lemma edgeSet_coe {G' : G.Subgraph} : G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet := by
  ext e; induction e using Sym2.ind; simp

lemma image_coe_edgeSet_coe (G' : G.Subgraph) : Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet := by
  rw [edgeSet_coe, Set.image_preimage_eq_iff]
  rintro e he
  induction e using Sym2.ind with | h a b =>
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨s(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩), Sym2.map_mk ..⟩

@[simp]
lemma edgeSet_spanningCoe (G' : G.Subgraph) : G'.spanningCoe.edgeSet = G'.edgeSet := by
  rfl

theorem mem_verts_of_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e ∈ G'.edgeSet)
    (hv : v ∈ e) : v ∈ G'.verts := by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
  · exact G'.edge_vert (G'.symm he)

/-- The `incidenceSet` is the set of edges incident to a given vertex. -/
def incidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V) := {e ∈ G'.edgeSet | v ∈ e}

theorem incidenceSet_subset_incidenceSet (G' : Subgraph G) (v : V) :
    G'.incidenceSet v ⊆ G.incidenceSet v :=
  fun _ h ↦ ⟨G'.edgeSet_subset h.1, h.2⟩

theorem incidenceSet_subset (G' : Subgraph G) (v : V) : G'.incidenceSet v ⊆ G'.edgeSet :=
  fun _ h ↦ h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
abbrev vert (G' : Subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : Subgraph G where
  verts := V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm

theorem copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G' :=
  Subgraph.ext hV hadj

/-- The union of two subgraphs. -/
instance : Max G.Subgraph where
  max G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm := fun _ _ => Or.imp G₁.adj_symm G₂.adj_symm }

/-- The intersection of two subgraphs. -/
instance : Min G.Subgraph where
  min G₁ G₂ :=
    { verts := G₁.verts ∩ G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm := fun _ _ => And.imp G₁.adj_symm G₂.adj_symm }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
instance : Top G.Subgraph where
  top :=
    { verts := Set.univ
      Adj := G.Adj
      adj_sub := id
      edge_vert := @fun v _ _ => Set.mem_univ v
      symm := G.symm }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
instance : Bot G.Subgraph where
  bot :=
    { verts := ∅
      Adj := ⊥
      adj_sub := False.elim
      edge_vert := False.elim
      symm := fun _ _ => id }

instance : SupSet G.Subgraph where
  sSup s :=
    { verts := ⋃ G' ∈ s, verts G'
      Adj := fun a b => ∃ G' ∈ s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_vert := by
        rintro a b ⟨G', hG', hab⟩
        exact Set.mem_iUnion₂_of_mem hG' (G'.edge_vert hab)
      symm := fun a b h => by simpa [adj_comm] using h }

instance : InfSet G.Subgraph where
  sInf s :=
    { verts := ⋂ G' ∈ s, verts G'
      Adj := fun a b => (∀ ⦃G'⦄, G' ∈ s → Adj G' a b) ∧ G.Adj a b
      adj_sub := And.right
      edge_vert := fun hab => Set.mem_iInter₂_of_mem fun G' hG' => G'.edge_vert <| hab.1 hG'
      symm := fun _ _ => And.imp (forall₂_imp fun _ _ => Adj.symm) G.adj_symm }

@[simp]
theorem sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b :=
  Iff.rfl

@[simp]
theorem inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b :=
  Iff.rfl

@[simp]
theorem top_adj : (⊤ : Subgraph G).Adj a b ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem not_bot_adj : ¬ (⊥ : Subgraph G).Adj a b :=
  not_false

@[simp]
theorem verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts :=
  rfl

@[simp]
theorem verts_inf (G₁ G₂ : G.Subgraph) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts :=
  rfl

@[simp]
theorem verts_top : (⊤ : G.Subgraph).verts = Set.univ :=
  rfl

@[simp]
theorem verts_bot : (⊥ : G.Subgraph).verts = ∅ :=
  rfl

theorem eq_bot_iff_verts_eq_empty (G' : G.Subgraph) : G' = ⊥ ↔ G'.verts = ∅ :=
  ⟨(· ▸ verts_bot), fun h ↦ Subgraph.ext (h ▸ verts_bot (G := G)) <|
    funext₂ fun _ _ ↦ propext ⟨fun h' ↦ (h ▸ h'.fst_mem :), False.elim⟩⟩

theorem ne_bot_iff_nonempty_verts (G' : G.Subgraph) : G' ≠ ⊥ ↔ G'.verts.Nonempty :=
  G'.eq_bot_iff_verts_eq_empty.not.trans <| Set.nonempty_iff_ne_empty.symm

@[simp]
theorem sSup_adj {s : Set G.Subgraph} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set G.Subgraph} : (sInf s).Adj a b ↔ (∀ G' ∈ s, Adj G' a b) ∧ G.Adj a b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → G.Subgraph} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
theorem iInf_adj {f : ι → G.Subgraph} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ G.Adj a b := by
  simp [iInf]

theorem sInf_adj_of_nonempty {s : Set G.Subgraph} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G' ∈ s, Adj G' a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → G.Subgraph} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]
theorem verts_sSup (s : Set G.Subgraph) : (sSup s).verts = ⋃ G' ∈ s, verts G' :=
  rfl

@[simp]
theorem verts_sInf (s : Set G.Subgraph) : (sInf s).verts = ⋂ G' ∈ s, verts G' :=
  rfl

@[simp]
theorem verts_iSup {f : ι → G.Subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by simp [iSup]

@[simp]
theorem verts_iInf {f : ι → G.Subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by simp [iInf]

@[simp] lemma coe_bot : (⊥ : G.Subgraph).coe = ⊥ := rfl

@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced := fun _ _ _ _ ↦ id

/-- The graph isomorphism between the top element of `G.subgraph` and `G`. -/
def topIso : (⊤ : G.Subgraph).coe ≃g G where
  toFun := (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl

theorem verts_spanningCoe_injective :
    (fun G' : Subgraph G => (G'.verts, G'.spanningCoe)).Injective := by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext h.1 (spanningCoe_inj.1 h.2)

/-- For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
instance : PartialOrder G.Subgraph where
  __ := PartialOrder.lift _ verts_spanningCoe_injective
  le x y := x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance distribLattice : DistribLattice G.Subgraph :=
  verts_spanningCoe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance : BoundedOrder (Subgraph G) where
  le_top x := ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

/-- Note that subgraphs do not form a Boolean algebra, because of `verts`. -/
@[implicit_reducible]
def completelyDistribLatticeMinimalAxioms : CompletelyDistribLattice.MinimalAxioms G.Subgraph where
  le_top G' := ⟨Set.subset_univ _, fun _ _ => G'.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩
  isLUB_sSup _ :=
    ⟨fun G' hG' ↦ ⟨Set.subset_biUnion_of_mem hG', fun _ _ hab => ⟨G', hG', hab⟩⟩,
      fun G' hG' ↦
        ⟨Set.iUnion₂_subset fun _ hH => (hG' hH).1, fun a b ⟨H, hH, hab⟩ ↦ (hG' hH).2 hab⟩⟩
  isGLB_sInf _ :=
    ⟨fun G' hG' ↦ ⟨Set.iInter₂_subset G' hG', fun _ _ hab => hab.1 hG'⟩,
      fun G' hG' ↦
        ⟨Set.subset_iInter₂ fun _ hH => (hG' hH).1, fun _ _ hab =>
          ⟨fun _ hH => (hG' hH).2 hab, G'.adj_sub hab⟩⟩⟩
  iInf_iSup_eq f := Subgraph.ext (by simpa using iInf_iSup_eq)
    (by ext; simp [Classical.skolem])

instance : CompletelyDistribLattice G.Subgraph :=
  fast_instance% .ofMinimalAxioms completelyDistribLatticeMinimalAxioms

@[gcongr] lemma verts_mono {H H' : G.Subgraph} (h : H ≤ H') : H.verts ⊆ H'.verts := h.1
lemma verts_monotone : Monotone (verts : G.Subgraph → Set V) := fun _ _ h ↦ h.1

@[simps]
instance subgraphInhabited : Inhabited (Subgraph G) := ⟨⊥⟩

@[simp]
theorem neighborSet_sup {H H' : G.Subgraph} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v := rfl

@[simp]
theorem neighborSet_inf {H H' : G.Subgraph} (v : V) :
    (H ⊓ H').neighborSet v = H.neighborSet v ∩ H'.neighborSet v := rfl

@[simp]
theorem neighborSet_top (v : V) : (⊤ : G.Subgraph).neighborSet v = G.neighborSet v := rfl

@[simp]
theorem neighborSet_bot (v : V) : (⊥ : G.Subgraph).neighborSet v = ∅ := rfl

@[simp]
theorem neighborSet_sSup (s : Set G.Subgraph) (v : V) :
    (sSup s).neighborSet v = ⋃ G' ∈ s, neighborSet G' v := by
  ext
  simp

@[simp]
theorem neighborSet_sInf (s : Set G.Subgraph) (v : V) :
    (sInf s).neighborSet v = (⋂ G' ∈ s, neighborSet G' v) ∩ G.neighborSet v := by
  ext
  simp

@[simp]
theorem neighborSet_iSup (f : ι → G.Subgraph) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by simp [iSup]

@[simp]
theorem neighborSet_iInf (f : ι → G.Subgraph) (v : V) :
    (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) ∩ G.neighborSet v := by simp [iInf]

@[simp]
theorem edgeSet_top : (⊤ : Subgraph G).edgeSet = G.edgeSet := rfl

@[simp]
theorem edgeSet_bot : (⊥ : Subgraph G).edgeSet = ∅ :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_inf {H₁ H₂ : Subgraph G} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet ∩ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_sSup (s : Set G.Subgraph) : (sSup s).edgeSet = ⋃ G' ∈ s, edgeSet G' := by
  ext e
  induction e
  simp

@[simp]
theorem edgeSet_sInf (s : Set G.Subgraph) :
    (sInf s).edgeSet = (⋂ G' ∈ s, edgeSet G') ∩ G.edgeSet := by
  ext e
  induction e
  simp

@[simp]
theorem edgeSet_iSup (f : ι → G.Subgraph) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by simp [iSup]

@[simp]
theorem edgeSet_iInf (f : ι → G.Subgraph) :
    (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) ∩ G.edgeSet := by
  simp [iInf]

@[simp]
theorem spanningCoe_top : (⊤ : Subgraph G).spanningCoe = G := rfl

@[simp]
theorem spanningCoe_bot : (⊥ : Subgraph G).spanningCoe = ⊥ := rfl

/-- Turn a subgraph of a `SimpleGraph` into a member of its subgraph type. -/
@[simps]
def _root_.SimpleGraph.toSubgraph (H : SimpleGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm

theorem support_mono {H H' : Subgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
  SetRel.dom_mono fun _ hvw ↦ h.2 hvw

theorem _root_.SimpleGraph.toSubgraph.isSpanning (H : SimpleGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

theorem spanningCoe_le_of_le {H H' : Subgraph G} (h : H ≤ H') : H.spanningCoe ≤ H'.spanningCoe :=
  h.2

@[simp]
lemma sup_spanningCoe (H H' : Subgraph G) :
    (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := rfl

/-- The bottom of the `Subgraph G` lattice is isomorphic to the empty graph on the empty
vertex type. -/
def botIso : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where
  toFun v := v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ ↦ h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl

theorem edgeSet_mono {H₁ H₂ : Subgraph G} (h : H₁ ≤ H₂) : H₁.edgeSet ≤ H₂.edgeSet :=
  Sym2.ind h.2

theorem _root_.Disjoint.edgeSet {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂) :
    Disjoint H₁.edgeSet H₂.edgeSet :=
  disjoint_iff_inf_le.mpr <| by simpa using edgeSet_mono h.le_bot

@[simp]
lemma disjoint_verts_iff_disjoint {H H' : Subgraph G} :
    Disjoint H.verts H'.verts ↔ Disjoint H H' := by
  constructor
  · rintro hdisj M' ⟨hsub₀, _⟩ ⟨hsub₁, _⟩
    rw [le_bot_iff]
    ext
    · grind [verts_bot]
    · exact ⟨(hdisj hsub₀ hsub₁ <| M'.edge_vert · :), False.elim⟩
  · intro hdisj S h₀ h₁ v hvS
    let M' : Subgraph G := { verts := {v}, Adj := ⊥, adj_sub := by simp, edge_vert := by simp }
    have hle {M : Subgraph G} (h : v ∈ M.verts) : M' ≤ M := by constructor <;> simp [h, M']
    exact hdisj (hle <| h₀ hvS) (hle <| h₁ hvS) |>.left <| Set.mem_singleton v

section map
variable {G' : SimpleGraph W} {f : G →g G'}

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
protected def map (f : G →g G') (H : G.Subgraph) : G'.Subgraph where
  verts := f '' H.verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ (H.edge_vert h)
  symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u, H.symm h, rfl, rfl⟩

@[simp] lemma map_id (H : G.Subgraph) : H.map Hom.id = H := by ext <;> simp

lemma map_comp {U : Type*} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G →g G') (g : G' →g G'') :
    H.map (g.comp f) = (H.map f).map g := by ext <;> simp [Subgraph.map]

@[gcongr] lemma map_mono {H₁ H₂ : G.Subgraph} (hH : H₁ ≤ H₂) : H₁.map f ≤ H₂.map f := by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩

lemma map_monotone : Monotone (Subgraph.map f) := fun _ _ ↦ map_mono

theorem map_sup (f : G →g G') (H₁ H₂ : G.Subgraph) : (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f := by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]

@[simp] lemma map_iso_top {H : SimpleGraph W} (e : G ≃g H) : Subgraph.map e.toHom ⊤ = ⊤ := by
  ext <;> simp [Relation.Map, e.apply_eq_iff_eq_symm_apply, ← e.map_rel_iff]

@[simp] lemma edgeSet_map (f : G →g G') (H : G.Subgraph) :
    (H.map f).edgeSet = Sym2.map f '' H.edgeSet := Sym2.fromRel_relationMap ..

end map

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
protected def comap {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) : G.Subgraph where
  verts := f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm _ _ h := ⟨G.symm h.1, H.symm h.2⟩

theorem comap_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2

@[simp] lemma comap_equiv_top {H : SimpleGraph W} (f : G →g H) : Subgraph.comap f ⊤ = ⊤ := by
  ext <;> simp +contextual [f.map_adj]

theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (H' : G'.Subgraph) :
    H.map f ≤ H' ↔ H ≤ H'.comap f := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, fun v w hvw ↦ ?_⟩, fun h ↦ ⟨fun v ↦ ?_, fun v w ↦ ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro w hw rfl
    exact h.1 hw
  · simp only [Relation.Map, map_adj, forall_exists_index, and_imp]
    rintro u u' hu rfl rfl
    exact (h.2 hu).2

instance [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.Subgraph := by
  refine .ofBijective
    (α := {H : Finset V × (V → V → Bool) //
      (∀ a b, H.2 a b → G.Adj a b) ∧ (∀ a b, H.2 a b → a ∈ H.1) ∧ ∀ a b, H.2 a b = H.2 b a})
    (fun H ↦ ⟨H.1.1, fun a b ↦ H.1.2 a b, @H.2.1, @H.2.2.1, by simp [Symmetric, H.2.2.2]⟩)
    ⟨?_, fun H ↦ ?_⟩
  · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
    simp [funext_iff]
  · classical
    exact ⟨⟨(H.verts.toFinset, fun a b ↦ H.Adj a b), fun a b ↦ by simpa using H.adj_sub,
      fun a b ↦ by simpa using H.edge_vert, by simp [H.adj_comm]⟩, by simp⟩

instance [Finite V] : Finite G.Subgraph := by classical cases nonempty_fintype V; infer_instance

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
def inclusion {x y : Subgraph G} (h : x ≤ y) : x.coe →g y.coe where
  toFun v := ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw

theorem inclusion.injective {x y : Subgraph G} (h : x ≤ y) : Function.Injective (inclusion h) :=
  fun _ _ h ↦ Subtype.ext congr(Subtype.val $h)

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
protected def hom (x : Subgraph G) : x.coe →g G where
  toFun v := v
  map_rel' := x.adj_sub

@[simp] lemma coe_hom (x : Subgraph G) :
    (x.hom : x.verts → V) = (fun (v : x.verts) => (v : V)) := rfl

theorem hom_injective {x : Subgraph G} : Function.Injective x.hom :=
  fun _ _ ↦ Subtype.ext

@[simp] lemma map_hom_top (G' : G.Subgraph) : Subgraph.map G'.hom ⊤ = G' := by
  aesop (add unfold safe Relation.Map, unsafe G'.edge_vert, unsafe Adj.symm)

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
def spanningHom (x : Subgraph G) : x.spanningCoe →g G where
  toFun := id
  map_rel' := x.adj_sub

theorem spanningHom_injective {x : Subgraph G} : Function.Injective x.spanningHom :=
  fun _ _ ↦ id

theorem neighborSet_subset_of_subgraph {x y : Subgraph G} (h : x ≤ y) (v : V) :
    x.neighborSet v ⊆ y.neighborSet v :=
  fun _ h' ↦ h.2 h'

instance neighborSet.decidablePred (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· ∈ G'.neighborSet v) :=
  h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
@[implicit_reducible]
def finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' ≤ G'') (v : G'.verts)
    [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)

instance (G' : Subgraph G) [Fintype G'.verts] (v : V) [DecidablePred (· ∈ G'.neighborSet v)] :
    Fintype (G'.neighborSet v) :=
  Set.fintypeSubset G'.verts (neighborSet_subset_verts G' v)

instance coeFiniteAt {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)] :
    Fintype (G'.coe.neighborSet v) :=
  Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm

theorem IsSpanning.card_verts [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning) :
    G'.verts.toFinset.card = Fintype.card V := by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

/-- The degree of a vertex in a subgraph. It's zero for vertices outside the subgraph. -/
def degree (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] : ℕ :=
  Fintype.card (G'.neighborSet v)

theorem finset_card_neighborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    (G'.neighborSet v).toFinset.card = G'.degree v := by
  rw [degree, Set.toFinset_card]

theorem degree_of_notMem_verts {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : v ∉ G'.verts) : G'.degree v = 0 := by
  rw [degree, Fintype.card_eq_zero_iff, isEmpty_subtype]
  intro w
  by_contra hw
  exact h hw.fst_mem

theorem degree_le (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G.neighborSet v)] : G'.degree v ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)

theorem degree_le' (G' G'' : Subgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G''.neighborSet v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]
theorem coe_degree (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
    [Fintype (G'.neighborSet v)] : G'.coe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)

@[simp]
theorem degree_spanningCoe {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree, Subgraph.degree]
  congr!

theorem degree_pos_iff_exists_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    0 < G'.degree v ↔ ∃ w, G'.Adj v w := by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

theorem degree_eq_zero_of_subsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    (hG : G'.verts.Subsingleton) : G'.degree v = 0 := by
  by_cases hv : v ∈ G'.verts
  · rw [← G'.coe_degree ⟨v, hv⟩]
    have := (Set.subsingleton_coe _).mpr hG
    exact G'.coe.degree_eq_zero_of_subsingleton ⟨v, hv⟩
  · exact degree_of_notMem_verts hv

theorem degree_eq_one_iff_existsUnique_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    G'.degree v = 1 ↔ ∃! w : V, G'.Adj v w := by
  rw [← finset_card_neighborSet_eq_degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]

@[deprecated (since := "2025-10-31")]
alias degree_eq_one_iff_unique_adj := degree_eq_one_iff_existsUnique_adj

theorem nontrivial_verts_of_degree_ne_zero {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : G'.degree v ≠ 0) : Nontrivial G'.verts := by
  by_contra
  simp_all [G'.degree_eq_zero_of_subsingleton v]

lemma neighborSet_eq_of_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    H.neighborSet v = G.neighborSet v := by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
  refine congrArg _ <| Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset, hs, ht]
  exact H.neighborSet_subset _

lemma adj_iff_of_neighborSet_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    ∀ {w}, H.Adj v w ↔ G.Adj v w :=
  Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

end Subgraph

@[simp]
theorem card_neighborSet_toSubgraph (G H : SimpleGraph V) (h : H ≤ G)
    (v : V) [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    Fintype.card ↑((toSubgraph H h).neighborSet v) = H.degree v := by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]
lemma degree_toSubgraph (G H : SimpleGraph V) (h : H ≤ G) {v : V}
    [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    (toSubgraph H h).degree v = H.degree v := by
  simp [Subgraph.degree]

section MkProperties

/-! ### Properties of `singletonSubgraph` and `subgraphOfAdj` -/


variable {G : SimpleGraph V} {G' : SimpleGraph W}

@[deprecated "Use the `Unique` instance instead." (since := "2025-10-21")]
instance nonempty_singletonSubgraph_verts (v : V) : Nonempty (G.singletonSubgraph v).verts :=
  ⟨⟨v, Set.mem_singleton v⟩⟩

instance (v : V) : Unique (G.singletonSubgraph v).verts :=
  Set.uniqueSingleton _

@[simp]
theorem singletonSubgraph_le_iff (v : V) (H : G.Subgraph) :
    G.singletonSubgraph v ≤ H ↔ v ∈ H.verts := by
  refine ⟨fun h ↦ h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ ↦ False.elim

@[simp]
theorem map_singletonSubgraph (f : G →g G') {v : V} :
    Subgraph.map f (G.singletonSubgraph v) = G'.singletonSubgraph (f v) := by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]
theorem neighborSet_singletonSubgraph (v w : V) : (G.singletonSubgraph v).neighborSet w = ∅ :=
  rfl

@[simp]
theorem edgeSet_singletonSubgraph (v : V) : (G.singletonSubgraph v).edgeSet = ∅ :=
  Sym2.fromRel_bot

theorem eq_singletonSubgraph_iff_verts_eq (H : G.Subgraph) {v : V} :
    H = G.singletonSubgraph v ↔ H.verts = {v} := by
  refine ⟨fun h ↦ by rw [h, singletonSubgraph_verts], fun h ↦ ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h, Set.mem_singleton_iff] at ha1 ha2
    subst_vars
    exact ha.ne rfl

instance nonempty_subgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) :
    Nonempty (G.subgraphOfAdj hvw).verts :=
  ⟨⟨v, by simp⟩⟩

@[simp]
theorem edgeSet_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).edgeSet = {s(v, w)} := by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj,
    forall₂_true_iff]

lemma subgraphOfAdj_le_of_adj {v w : V} (H : G.Subgraph) (h : H.Adj v w) :
    G.subgraphOfAdj (H.adj_sub h) ≤ H := by
  constructor
  · intro x
    rintro (rfl | rfl) <;> simp [H.edge_vert h, H.edge_vert h.symm]
  · simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff]
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [h, h.symm]

theorem subgraphOfAdj_symm {v w : V} (hvw : G.Adj v w) :
    G.subgraphOfAdj hvw.symm = G.subgraphOfAdj hvw := by
  ext <;> simp [or_comm, and_comm]

@[simp]
theorem map_subgraphOfAdj (f : G →g G') {v w : V} (hvw : G.Adj v w) :
    Subgraph.map f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f.map_adj hvw) := by
  ext <;> grind [Subgraph.map_verts, subgraphOfAdj_verts, Relation.Map, Subgraph.map_adj,
    subgraphOfAdj_adj]

theorem neighborSet_subgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u ⊆ {v, w} :=
  (G.subgraphOfAdj hvw).neighborSet_subset_verts _

@[simp]
theorem neighborSet_fst_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet v = {w} := by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]
theorem neighborSet_snd_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet w = {v} := by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm

@[simp]
theorem neighborSet_subgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u ≠ v)
    (hw : u ≠ w) : (G.subgraphOfAdj hvw).neighborSet u = ∅ := by
  ext
  simp [hv.symm, hw.symm]

theorem neighborSet_subgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u =
    (if u = v then {w} else ∅) ∪ if u = w then {v} else ∅ := by
  split_ifs <;> subst_vars <;> simp [*]

theorem singletonSubgraph_fst_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph u ≤ G.subgraphOfAdj h := by
  simp

theorem singletonSubgraph_snd_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph v ≤ G.subgraphOfAdj h := by
  simp

@[simp]
lemma support_subgraphOfAdj {u v : V} (h : G.Adj u v) :
    (G.subgraphOfAdj h).support = {u, v} := by
  ext
  rw [Subgraph.mem_support]
  simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h ↦ h.elim (fun hl ↦ ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr ↦ ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 ↦ .inl h1.1.symm) fun hr ↦ .inr hr.2.symm

end MkProperties

namespace Subgraph

variable {G : SimpleGraph V}

/-! ### Subgraphs of subgraphs -/


/-- Given a subgraph of a subgraph of `G`, construct a subgraph of `G`. -/
protected abbrev coeSubgraph {G' : G.Subgraph} : G'.coe.Subgraph → G.Subgraph :=
  Subgraph.map G'.hom

/-- Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
protected abbrev restrict {G' : G.Subgraph} : G.Subgraph → G'.coe.Subgraph :=
  Subgraph.comap G'.hom

@[simp]
lemma verts_coeSubgraph {G' : Subgraph G} (G'' : Subgraph G'.coe) :
    (Subgraph.coeSubgraph G'').verts = (G''.verts : Set V) := rfl

lemma coeSubgraph_adj {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V) :
    (G'.coeSubgraph G'').Adj v w ↔
      ∃ (hv : v ∈ G'.verts) (hw : w ∈ G'.verts), G''.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp [Relation.Map]

lemma restrict_adj {G' G'' : G.Subgraph} (v w : G'.verts) :
    (G'.restrict G'').Adj v w ↔ G'.Adj v w ∧ G''.Adj v w := Iff.rfl

theorem restrict_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph) :
    Subgraph.restrict (Subgraph.coeSubgraph G'') = G'' := by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub

theorem coeSubgraph_injective (G' : G.Subgraph) :
    Function.Injective (Subgraph.coeSubgraph : G'.coe.Subgraph → G.Subgraph) :=
  Function.LeftInverse.injective restrict_coeSubgraph

lemma coeSubgraph_le {H : G.Subgraph} (H' : H.coe.Subgraph) :
    Subgraph.coeSubgraph H' ≤ H := by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

lemma coeSubgraph_restrict_eq {H : G.Subgraph} (H' : G.Subgraph) :
    Subgraph.coeSubgraph (H.restrict H') = H ⊓ H' := by
  ext
  · simp
  · simp_rw [coeSubgraph_adj, restrict_adj]
    simp only [exists_and_left, exists_prop, inf_adj, and_congr_right_iff]
    intro h
    simp [H.edge_vert h, H.edge_vert h.symm]

/-! ### Edge deletion -/


/-- Given a subgraph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present.

See also: `SimpleGraph.deleteEdges`. -/
def deleteEdges (G' : G.Subgraph) (s : Set (Sym2 V)) : G.Subgraph where
  verts := G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub h' := G'.adj_sub h'.1
  edge_vert h' := G'.edge_vert h'.1
  symm a b := by simp [G'.adj_comm, Sym2.eq_swap]

section DeleteEdges

variable {G' : G.Subgraph} (s : Set (Sym2 V))

@[simp]
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl

@[simp]
theorem deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s :=
  Iff.rfl

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext <;> simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
theorem deleteEdges_spanningCoe_eq :
    G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp

theorem deleteEdges_coe_eq (s : Set (Sym2 G'.verts)) :
    G'.coe.deleteEdges s = (G'.deleteEdges (Sym2.map (↑) '' s)).coe := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [SimpleGraph.deleteEdges_adj, coe_adj, deleteEdges_adj, Set.mem_image, not_exists,
    not_and, and_congr_right_iff]
  intro
  constructor
  · intro hs
    refine Sym2.ind ?_
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [Sym2.map_mk, Sym2.eq]
    contrapose
    rintro (_ | _) <;> simpa only [Sym2.eq_swap]
  · intro h' hs
    exact h' _ hs rfl

theorem coe_deleteEdges_eq (s : Set (Sym2 V)) :
    (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map (↑) ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp

theorem deleteEdges_le : G'.deleteEdges s ≤ G' := by
  constructor <;> simp +contextual

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs ↦ hs' (h hs)

@[simp]
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp +contextual

@[simp]
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp +contextual [imp_false]

theorem coe_deleteEdges_le : (G'.deleteEdges s).coe ≤ (G'.coe : SimpleGraph G'.verts) := by
  intro v w
  simp +contextual

theorem spanningCoe_deleteEdges_le (G' : G.Subgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe ≤ G'.spanningCoe :=
  spanningCoe_le_of_le (deleteEdges_le s)

end DeleteEdges

/-! ### Induced subgraphs -/


/- Given a subgraph, we can change its vertex set while removing any invalid edges, which
gives induced subgraphs. See also `SimpleGraph.induce` for the `SimpleGraph` version, which,
unlike for subgraphs, results in a graph with a different vertex type. -/
/-- The induced subgraph of a subgraph. The expectation is that `s ⊆ G'.verts` for the usual
notion of an induced subgraph, but, in general, `s` is taken to be the new vertex set and edges
are induced from the subgraph `G'`. -/
@[simps]
def induce (G' : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj u v := u ∈ s ∧ v ∈ s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm _ _ h := ⟨h.2.1, h.1, G'.symm h.2.2⟩

theorem _root_.SimpleGraph.induce_eq_coe_induce_top (s : Set V) :
    G.induce s = ((⊤ : G.Subgraph).induce s).coe := by
  ext
  simp

lemma _root_.SimpleGraph.spanningCoe_induce_top (s : Set V) :
    ((⊤ : G.Subgraph).induce s).spanningCoe = (G.induce s).spanningCoe := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  `grind [induce_eq_coe_induce_top, Subgraph.spanningCoe_coe]` -/
  rw [induce_eq_coe_induce_top]
  exact (Subgraph.spanningCoe_coe _).symm

section Induce

variable {G' G'' : G.Subgraph} {s s' : Set V}

@[simp]
theorem IsInduced.induce_top_verts (h : G'.IsInduced) : induce ⊤ G'.verts = G' :=
  Subgraph.ext rfl <| funext₂ fun _ _ ↦ propext
    ⟨fun ⟨hu, hv, h'⟩ ↦ h hu hv h', fun h ↦ ⟨G'.edge_vert h, G'.edge_vert h.symm, h.adj_sub⟩⟩

theorem isInduced_iff_exists_eq_induce_top (G' : G.Subgraph) :
    G'.IsInduced ↔ ∃ s, G' = induce ⊤ s := by
  refine ⟨fun h ↦ ⟨G'.verts, h.induce_top_verts.symm⟩, fun ⟨s, h⟩ _ hu _ hv hadj ↦ ?_⟩
  rw [h, (h ▸ rfl : s = G'.verts)]
  exact ⟨hu, hv, hadj⟩

@[gcongr]
theorem induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' := by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[mono]
theorem induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s :=
  induce_mono hg subset_rfl

@[mono]
theorem induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' :=
  induce_mono le_rfl hs

@[simp]
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp

@[simp]
theorem induce_self_verts : G'.induce G'.verts = G' := by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha ↦ ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩

lemma le_induce_top_verts : G' ≤ (⊤ : G.Subgraph).induce G'.verts :=
  calc G' = G'.induce G'.verts := Subgraph.induce_self_verts.symm
       _ ≤ (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top

lemma le_induce_union : G'.induce s ⊔ G'.induce s' ≤ G'.induce (s ∪ s') := by
  constructor
  · simp only [verts_sup, induce_verts, Set.Subset.rfl]
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

lemma le_induce_union_left : G'.induce s ≤ G'.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).1

lemma le_induce_union_right : G'.induce s' ≤ G'.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).2

theorem singletonSubgraph_eq_induce {v : V} :
    G.singletonSubgraph v = (⊤ : G.Subgraph).induce {v} := by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]

theorem subgraphOfAdj_eq_induce {v w : V} (hvw : G.Adj v w) :
    G.subgraphOfAdj hvw = (⊤ : G.Subgraph).induce {v, w} := by
  ext
  · simp
  · constructor
    · intro h
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff] at h
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hvw, hvw.symm]
    · intro h
      simp only [induce_adj, Set.mem_insert_iff, Set.mem_singleton_iff, top_adj] at h
      obtain ⟨rfl | rfl, rfl | rfl, ha⟩ := h <;> first | exact (ha.ne rfl).elim | simp

instance instDecidableRel_induce_adj (s : Set V) [∀ a, Decidable (a ∈ s)] [DecidableRel G'.Adj] :
    DecidableRel (G'.induce s).Adj :=
  fun _ _ ↦ instDecidableAnd

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between an induced subgraph and its corresponding simple graph. -/
def coeInduceIso (s : Set V) (h : s ⊆ G'.verts) :
    (G'.induce s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∈ s} where
  toFun := fun ⟨v, hv⟩ ↦ ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ ↦ ⟨v, hv⟩
  map_rel_iff' := by simp

end Induce

/-- Given a subgraph and a set of vertices, delete all the vertices from the subgraph,
if present. Any edges incident to the deleted vertices are deleted as well. -/
abbrev deleteVerts (G' : G.Subgraph) (s : Set V) : G.Subgraph :=
  G'.induce (G'.verts \ s)

section DeleteVerts

variable {G' : G.Subgraph} {s : Set V}

theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl

theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ u ∉ s ∧ v ∈ G'.verts ∧ v ∉ s ∧ G'.Adj u v := by
  simp [and_assoc]

@[simp]
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s ∪ s') := by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]
theorem deleteVerts_empty : G'.deleteVerts ∅ = G' := by
  simp [deleteVerts]

theorem deleteVerts_le : G'.deleteVerts s ≤ G' := by
  constructor <;> simp

@[gcongr, mono]
theorem deleteVerts_mono {G' G'' : G.Subgraph} (h : G' ≤ G'') :
    G'.deleteVerts s ≤ G''.deleteVerts s :=
  induce_mono h (Set.diff_subset_diff_left h.1)

@[mono]
lemma deleteVerts_mono' {G' : SimpleGraph V} (u : Set V) (h : G ≤ G') :
    ((⊤ : Subgraph G).deleteVerts u).coe ≤ ((⊤ : Subgraph G').deleteVerts u).coe := by
  intro v w hvw
  aesop

@[gcongr, mono]
theorem deleteVerts_anti {s s' : Set V} (h : s ⊆ s') : G'.deleteVerts s' ≤ G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.diff_subset_diff_right h)

@[simp]
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts ∩ s) = G'.deleteVerts s := by
  ext <;> simp +contextual

@[simp]
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s ∩ G'.verts) = G'.deleteVerts s := by
  ext <;> simp +contextual

instance instDecidableRel_deleteVerts_adj (u : Set V) [r : DecidableRel G.Adj] :
    DecidableRel ((⊤ : G.Subgraph).deleteVerts u).coe.Adj :=
  fun x y =>
    if h : G.Adj x y
    then
      .isTrue <| SimpleGraph.Subgraph.Adj.coe <| Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, x.2.2, by trivial, y.2.2, h⟩
    else
      .isFalse <| fun hadj ↦ h <| Subgraph.coe_adj_sub _ _ _ hadj

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between a subgraph with deleted vertices and its corresponding simple graph. -/
def coeDeleteVertsIso (s : Set V) :
    (G'.deleteVerts s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∉ s} where
  toFun := fun ⟨v, hv⟩ ↦ ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ ↦ ⟨v, by simp_all⟩
  map_rel_iff' := by simp

end DeleteVerts

end Subgraph

end SimpleGraph
