/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

#align_import combinatorics.simple_graph.subgraph from "leanprover-community/mathlib"@"c6ef6387ede9983aee397d442974e61f89dfd87b"

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

## Todo

* Images of graph homomorphisms as subgraphs.

-/


universe u v

namespace SimpleGraph

/-- A subgraph of a `SimpleGraph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `Set (V × V)`, a set of darts (i.e., half-edges), then
`Subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure Subgraph {V : Type u} (G : SimpleGraph V) where
  verts : Set V
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, Adj v w → G.Adj v w
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Symmetric Adj := by aesop_graph -- Porting note: Originally `by obviously`
#align simple_graph.subgraph SimpleGraph.Subgraph

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
#align simple_graph.singleton_subgraph SimpleGraph.singletonSubgraph

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
#align simple_graph.subgraph_of_adj SimpleGraph.subgraphOfAdj

namespace Subgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.Subgraph} {a b : V}

protected theorem loopless (G' : Subgraph G) : Irreflexive G'.Adj :=
  fun v h ↦ G.loopless v (G'.adj_sub h)
#align simple_graph.subgraph.loopless SimpleGraph.Subgraph.loopless

theorem adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  ⟨fun x ↦ G'.symm x, fun x ↦ G'.symm x⟩
#align simple_graph.subgraph.adj_comm SimpleGraph.Subgraph.adj_comm

@[symm]
theorem adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h
#align simple_graph.subgraph.adj_symm SimpleGraph.Subgraph.adj_symm

protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h
#align simple_graph.subgraph.adj.symm SimpleGraph.Subgraph.Adj.symm

protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h
#align simple_graph.subgraph.adj.adj_sub SimpleGraph.Subgraph.Adj.adj_sub

protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert h
#align simple_graph.subgraph.adj.fst_mem SimpleGraph.Subgraph.Adj.fst_mem

protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  h.symm.fst_mem
#align simple_graph.subgraph.adj.snd_mem SimpleGraph.Subgraph.Adj.snd_mem

protected theorem Adj.ne {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ≠ v :=
  h.adj_sub.ne
#align simple_graph.subgraph.adj.ne SimpleGraph.Subgraph.Adj.ne

/-- Coercion from `G' : Subgraph G` to a `SimpleGraph G'.verts`. -/
@[simps]
protected def coe (G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm _ _ h := G'.symm h
  loopless v h := loopless G v (G'.adj_sub h)
#align simple_graph.subgraph.coe SimpleGraph.Subgraph.coe

@[simp]
theorem coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h
#align simple_graph.subgraph.coe_adj_sub SimpleGraph.Subgraph.coe_adj_sub

-- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
protected theorem Adj.coe {H : G.Subgraph} {u v : V} (h : H.Adj u v) :
    H.coe.Adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert h.symm⟩ := h
#align simple_graph.subgraph.adj.coe SimpleGraph.Subgraph.Adj.coe

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (G' : Subgraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts
#align simple_graph.subgraph.is_spanning SimpleGraph.Subgraph.IsSpanning

theorem isSpanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm
#align simple_graph.subgraph.is_spanning_iff SimpleGraph.Subgraph.isSpanning_iff

/-- Coercion from `Subgraph G` to `SimpleGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (G' : Subgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless v hv := G.loopless v (G'.adj_sub hv)
#align simple_graph.subgraph.spanning_coe SimpleGraph.Subgraph.spanningCoe

@[simp]
theorem Adj.of_spanningCoe {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v) :
    G.Adj u v :=
  G'.adj_sub h
#align simple_graph.subgraph.adj.of_spanning_coe SimpleGraph.Subgraph.Adj.of_spanningCoe

theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  simp [Subgraph.spanningCoe]
#align simple_graph.subgraph.spanning_coe_inj SimpleGraph.Subgraph.spanningCoe_inj

/-- `spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`. -/
@[simps]
def spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) :
    G'.spanningCoe ≃g G'.coe where
  toFun v := ⟨v, h v⟩
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align simple_graph.subgraph.spanning_coe_equiv_coe_of_spanning SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def IsInduced (G' : Subgraph G) : Prop :=
  ∀ {v w : V}, v ∈ G'.verts → w ∈ G'.verts → G.Adj v w → G'.Adj v w
#align simple_graph.subgraph.is_induced SimpleGraph.Subgraph.IsInduced

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (H : Subgraph G) : Set V := Rel.dom H.Adj
#align simple_graph.subgraph.support SimpleGraph.Subgraph.support

theorem mem_support (H : Subgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.Adj v w := Iff.rfl
#align simple_graph.subgraph.mem_support SimpleGraph.Subgraph.mem_support

theorem support_subset_verts (H : Subgraph G) : H.support ⊆ H.verts :=
  fun _ ⟨_, h⟩ ↦ H.edge_vert h
#align simple_graph.subgraph.support_subset_verts SimpleGraph.Subgraph.support_subset_verts

/-- `G'.neighborSet v` is the set of vertices adjacent to `v` in `G'`. -/
def neighborSet (G' : Subgraph G) (v : V) : Set V := {w | G'.Adj v w}
#align simple_graph.subgraph.neighbor_set SimpleGraph.Subgraph.neighborSet

theorem neighborSet_subset (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G.neighborSet v :=
  fun _ ↦ G'.adj_sub
#align simple_graph.subgraph.neighbor_set_subset SimpleGraph.Subgraph.neighborSet_subset

theorem neighborSet_subset_verts (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G'.verts :=
  fun _ h ↦ G'.edge_vert (adj_symm G' h)
#align simple_graph.subgraph.neighbor_set_subset_verts SimpleGraph.Subgraph.neighborSet_subset_verts

@[simp]
theorem mem_neighborSet (G' : Subgraph G) (v w : V) : w ∈ G'.neighborSet v ↔ G'.Adj v w := Iff.rfl
#align simple_graph.subgraph.mem_neighbor_set SimpleGraph.Subgraph.mem_neighborSet

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coeNeighborSetEquiv {G' : Subgraph G} (v : G'.verts) :
    G'.coe.neighborSet v ≃ G'.neighborSet v where
  toFun w := ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align simple_graph.subgraph.coe_neighbor_set_equiv SimpleGraph.Subgraph.coeNeighborSetEquiv

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edgeSet (G' : Subgraph G) : Set (Sym2 V) := Sym2.fromRel G'.symm
#align simple_graph.subgraph.edge_set SimpleGraph.Subgraph.edgeSet

theorem edgeSet_subset (G' : Subgraph G) : G'.edgeSet ⊆ G.edgeSet :=
  Sym2.ind (fun _ _ ↦ G'.adj_sub)
#align simple_graph.subgraph.edge_set_subset SimpleGraph.Subgraph.edgeSet_subset

@[simp]
theorem mem_edgeSet {G' : Subgraph G} {v w : V} : s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w := Iff.rfl
#align simple_graph.subgraph.mem_edge_set SimpleGraph.Subgraph.mem_edgeSet

theorem mem_verts_if_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e ∈ G'.edgeSet)
    (hv : v ∈ e) : v ∈ G'.verts := by
  revert hv
  refine Sym2.ind (fun v w he ↦ ?_) e he
  intro hv
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
  · exact G'.edge_vert (G'.symm he)
#align simple_graph.subgraph.mem_verts_if_mem_edge SimpleGraph.Subgraph.mem_verts_if_mem_edge

/-- The `incidenceSet` is the set of edges incident to a given vertex. -/
def incidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V) := {e ∈ G'.edgeSet | v ∈ e}
#align simple_graph.subgraph.incidence_set SimpleGraph.Subgraph.incidenceSet

theorem incidenceSet_subset_incidenceSet (G' : Subgraph G) (v : V) :
    G'.incidenceSet v ⊆ G.incidenceSet v :=
  fun _ h ↦ ⟨G'.edgeSet_subset h.1, h.2⟩
#align simple_graph.subgraph.incidence_set_subset_incidence_set SimpleGraph.Subgraph.incidenceSet_subset_incidenceSet

theorem incidenceSet_subset (G' : Subgraph G) (v : V) : G'.incidenceSet v ⊆ G'.edgeSet :=
  fun _ h ↦ h.1
#align simple_graph.subgraph.incidence_set_subset SimpleGraph.Subgraph.incidenceSet_subset

/-- Give a vertex as an element of the subgraph's vertex type. -/
abbrev vert (G' : Subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩
#align simple_graph.subgraph.vert SimpleGraph.Subgraph.vert

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
#align simple_graph.subgraph.copy SimpleGraph.Subgraph.copy

theorem copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G' :=
  Subgraph.ext _ _ hV hadj
#align simple_graph.subgraph.copy_eq SimpleGraph.Subgraph.copy_eq

/-- The union of two subgraphs. -/
instance : Sup G.Subgraph where
  sup G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm := fun _ _ => Or.imp G₁.adj_symm G₂.adj_symm }

/-- The intersection of two subgraphs. -/
instance : Inf G.Subgraph where
  inf G₁ G₂ :=
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
#align simple_graph.subgraph.sup_adj SimpleGraph.Subgraph.sup_adj

@[simp]
theorem inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b :=
  Iff.rfl
#align simple_graph.subgraph.inf_adj SimpleGraph.Subgraph.inf_adj

@[simp]
theorem top_adj : (⊤ : Subgraph G).Adj a b ↔ G.Adj a b :=
  Iff.rfl
#align simple_graph.subgraph.top_adj SimpleGraph.Subgraph.top_adj

@[simp]
theorem not_bot_adj : ¬ (⊥ : Subgraph G).Adj a b :=
  not_false
#align simple_graph.subgraph.not_bot_adj SimpleGraph.Subgraph.not_bot_adj

@[simp]
theorem verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts :=
  rfl
#align simple_graph.subgraph.verts_sup SimpleGraph.Subgraph.verts_sup

@[simp]
theorem verts_inf (G₁ G₂ : G.Subgraph) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts :=
  rfl
#align simple_graph.subgraph.verts_inf SimpleGraph.Subgraph.verts_inf

@[simp]
theorem verts_top : (⊤ : G.Subgraph).verts = Set.univ :=
  rfl
#align simple_graph.subgraph.verts_top SimpleGraph.Subgraph.verts_top

@[simp]
theorem verts_bot : (⊥ : G.Subgraph).verts = ∅ :=
  rfl
#align simple_graph.subgraph.verts_bot SimpleGraph.Subgraph.verts_bot

@[simp]
theorem sSup_adj {s : Set G.Subgraph} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl
#align simple_graph.subgraph.Sup_adj SimpleGraph.Subgraph.sSup_adj

@[simp]
theorem sInf_adj {s : Set G.Subgraph} : (sInf s).Adj a b ↔ (∀ G' ∈ s, Adj G' a b) ∧ G.Adj a b :=
  Iff.rfl
#align simple_graph.subgraph.Inf_adj SimpleGraph.Subgraph.sInf_adj

@[simp]
theorem iSup_adj {f : ι → G.Subgraph} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]
#align simple_graph.subgraph.supr_adj SimpleGraph.Subgraph.iSup_adj

@[simp]
theorem iInf_adj {f : ι → G.Subgraph} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ G.Adj a b := by
  simp [iInf]
#align simple_graph.subgraph.infi_adj SimpleGraph.Subgraph.iInf_adj

theorem sInf_adj_of_nonempty {s : Set G.Subgraph} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G' ∈ s, Adj G' a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')
#align simple_graph.subgraph.Inf_adj_of_nonempty SimpleGraph.Subgraph.sInf_adj_of_nonempty

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → G.Subgraph} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp
#align simple_graph.subgraph.infi_adj_of_nonempty SimpleGraph.Subgraph.iInf_adj_of_nonempty

@[simp]
theorem verts_sSup (s : Set G.Subgraph) : (sSup s).verts = ⋃ G' ∈ s, verts G' :=
  rfl
#align simple_graph.subgraph.verts_Sup SimpleGraph.Subgraph.verts_sSup

@[simp]
theorem verts_sInf (s : Set G.Subgraph) : (sInf s).verts = ⋂ G' ∈ s, verts G' :=
  rfl
#align simple_graph.subgraph.verts_Inf SimpleGraph.Subgraph.verts_sInf

@[simp]
theorem verts_iSup {f : ι → G.Subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by simp [iSup]
#align simple_graph.subgraph.verts_supr SimpleGraph.Subgraph.verts_iSup

@[simp]
theorem verts_iInf {f : ι → G.Subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by simp [iInf]
#align simple_graph.subgraph.verts_infi SimpleGraph.Subgraph.verts_iInf

theorem verts_spanningCoe_injective :
    (fun G' : Subgraph G => (G'.verts, G'.spanningCoe)).Injective := by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext _ _ h.1 (spanningCoe_inj.1 h.2)

/-- For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
instance distribLattice : DistribLattice G.Subgraph :=
  { show DistribLattice G.Subgraph from
      verts_spanningCoe_injective.distribLattice _
        (fun _ _ => rfl) fun _ _ => rfl with
    le := fun x y => x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w }

instance : BoundedOrder (Subgraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

-- Note that subgraphs do not form a Boolean algebra, because of `verts`.
instance : CompletelyDistribLattice G.Subgraph :=
  { Subgraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥
    le_top := fun G' => ⟨Set.subset_univ _, fun a b => G'.adj_sub⟩
    bot_le := fun G' => ⟨Set.empty_subset _, fun a b => False.elim⟩
    sSup := sSup
    -- Porting note: needed `apply` here to modify elaboration; previously the term itself was fine.
    le_sSup := fun s G' hG' => ⟨by apply Set.subset_iUnion₂ G' hG', fun a b hab => ⟨G', hG', hab⟩⟩
    sSup_le := fun s G' hG' =>
      ⟨Set.iUnion₂_subset fun H hH => (hG' _ hH).1, by
        rintro a b ⟨H, hH, hab⟩
        exact (hG' _ hH).2 hab⟩
    sInf := sInf
    sInf_le := fun s G' hG' => ⟨Set.iInter₂_subset G' hG', fun a b hab => hab.1 hG'⟩
    le_sInf := fun s G' hG' =>
      ⟨Set.subset_iInter₂ fun H hH => (hG' _ hH).1, fun a b hab =>
        ⟨fun H hH => (hG' _ hH).2 hab, G'.adj_sub hab⟩⟩
    iInf_iSup_eq := fun f => Subgraph.ext _ _ (by simpa using iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }

@[simps]
instance subgraphInhabited : Inhabited (Subgraph G) := ⟨⊥⟩
#align simple_graph.subgraph.subgraph_inhabited SimpleGraph.Subgraph.subgraphInhabited

@[simp]
theorem neighborSet_sup {H H' : G.Subgraph} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v := rfl
#align simple_graph.subgraph.neighbor_set_sup SimpleGraph.Subgraph.neighborSet_sup

@[simp]
theorem neighborSet_inf {H H' : G.Subgraph} (v : V) :
    (H ⊓ H').neighborSet v = H.neighborSet v ∩ H'.neighborSet v := rfl
#align simple_graph.subgraph.neighbor_set_inf SimpleGraph.Subgraph.neighborSet_inf

@[simp]
theorem neighborSet_top (v : V) : (⊤ : G.Subgraph).neighborSet v = G.neighborSet v := rfl
#align simple_graph.subgraph.neighbor_set_top SimpleGraph.Subgraph.neighborSet_top

@[simp]
theorem neighborSet_bot (v : V) : (⊥ : G.Subgraph).neighborSet v = ∅ := rfl
#align simple_graph.subgraph.neighbor_set_bot SimpleGraph.Subgraph.neighborSet_bot

@[simp]
theorem neighborSet_sSup (s : Set G.Subgraph) (v : V) :
    (sSup s).neighborSet v = ⋃ G' ∈ s, neighborSet G' v := by
  ext
  simp
#align simple_graph.subgraph.neighbor_set_Sup SimpleGraph.Subgraph.neighborSet_sSup

@[simp]
theorem neighborSet_sInf (s : Set G.Subgraph) (v : V) :
    (sInf s).neighborSet v = (⋂ G' ∈ s, neighborSet G' v) ∩ G.neighborSet v := by
  ext
  simp
#align simple_graph.subgraph.neighbor_set_Inf SimpleGraph.Subgraph.neighborSet_sInf

@[simp]
theorem neighborSet_iSup (f : ι → G.Subgraph) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by simp [iSup]
#align simple_graph.subgraph.neighbor_set_supr SimpleGraph.Subgraph.neighborSet_iSup

@[simp]
theorem neighborSet_iInf (f : ι → G.Subgraph) (v : V) :
    (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) ∩ G.neighborSet v := by simp [iInf]
#align simple_graph.subgraph.neighbor_set_infi SimpleGraph.Subgraph.neighborSet_iInf

@[simp]
theorem edgeSet_top : (⊤ : Subgraph G).edgeSet = G.edgeSet := rfl
#align simple_graph.subgraph.edge_set_top SimpleGraph.Subgraph.edgeSet_top

@[simp]
theorem edgeSet_bot : (⊥ : Subgraph G).edgeSet = ∅ :=
  Set.ext <| Sym2.ind (by simp)
#align simple_graph.subgraph.edge_set_bot SimpleGraph.Subgraph.edgeSet_bot

@[simp]
theorem edgeSet_inf {H₁ H₂ : Subgraph G} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet ∩ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)
#align simple_graph.subgraph.edge_set_inf SimpleGraph.Subgraph.edgeSet_inf

@[simp]
theorem edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)
#align simple_graph.subgraph.edge_set_sup SimpleGraph.Subgraph.edgeSet_sup

@[simp]
theorem edgeSet_sSup (s : Set G.Subgraph) : (sSup s).edgeSet = ⋃ G' ∈ s, edgeSet G' := by
  ext e
  induction e using Sym2.ind
  simp
#align simple_graph.subgraph.edge_set_Sup SimpleGraph.Subgraph.edgeSet_sSup

@[simp]
theorem edgeSet_sInf (s : Set G.Subgraph) :
    (sInf s).edgeSet = (⋂ G' ∈ s, edgeSet G') ∩ G.edgeSet := by
  ext e
  induction e using Sym2.ind
  simp
#align simple_graph.subgraph.edge_set_Inf SimpleGraph.Subgraph.edgeSet_sInf

@[simp]
theorem edgeSet_iSup (f : ι → G.Subgraph) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by simp [iSup]
#align simple_graph.subgraph.edge_set_supr SimpleGraph.Subgraph.edgeSet_iSup

@[simp]
theorem edgeSet_iInf (f : ι → G.Subgraph) :
    (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) ∩ G.edgeSet := by
  simp [iInf]
#align simple_graph.subgraph.edge_set_infi SimpleGraph.Subgraph.edgeSet_iInf

@[simp]
theorem spanningCoe_top : (⊤ : Subgraph G).spanningCoe = G := rfl
#align simple_graph.subgraph.spanning_coe_top SimpleGraph.Subgraph.spanningCoe_top

@[simp]
theorem spanningCoe_bot : (⊥ : Subgraph G).spanningCoe = ⊥ := rfl
#align simple_graph.subgraph.spanning_coe_bot SimpleGraph.Subgraph.spanningCoe_bot

/-- Turn a subgraph of a `SimpleGraph` into a member of its subgraph type. -/
@[simps]
def _root_.SimpleGraph.toSubgraph (H : SimpleGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm
#align simple_graph.to_subgraph SimpleGraph.toSubgraph

theorem support_mono {H H' : Subgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
  Rel.dom_mono h.2
#align simple_graph.subgraph.support_mono SimpleGraph.Subgraph.support_mono

theorem _root_.SimpleGraph.toSubgraph.isSpanning (H : SimpleGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ
#align simple_graph.to_subgraph.is_spanning SimpleGraph.toSubgraph.isSpanning

theorem spanningCoe_le_of_le {H H' : Subgraph G} (h : H ≤ H') : H.spanningCoe ≤ H'.spanningCoe :=
  h.2
#align simple_graph.subgraph.spanning_coe_le_of_le SimpleGraph.Subgraph.spanningCoe_le_of_le

/-- The top of the `Subgraph G` lattice is equivalent to the graph itself. -/
def topEquiv : (⊤ : Subgraph G).coe ≃g G where
  toFun v := ↑v
  invFun v := ⟨v, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
#align simple_graph.subgraph.top_equiv SimpleGraph.Subgraph.topEquiv

/-- The bottom of the `Subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def botEquiv : (⊥ : Subgraph G).coe ≃g (⊥ : SimpleGraph Empty) where
  toFun v := v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ ↦ h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl
#align simple_graph.subgraph.bot_equiv SimpleGraph.Subgraph.botEquiv

theorem edgeSet_mono {H₁ H₂ : Subgraph G} (h : H₁ ≤ H₂) : H₁.edgeSet ≤ H₂.edgeSet :=
  Sym2.ind h.2
#align simple_graph.subgraph.edge_set_mono SimpleGraph.Subgraph.edgeSet_mono

theorem _root_.Disjoint.edgeSet {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂) :
    Disjoint H₁.edgeSet H₂.edgeSet :=
  disjoint_iff_inf_le.mpr <| by simpa using edgeSet_mono h.le_bot
#align disjoint.edge_set Disjoint.edgeSet

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
protected def map {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) : G'.Subgraph where
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
#align simple_graph.subgraph.map SimpleGraph.Subgraph.map

theorem map_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.map f) := by
  intro H H' h
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, h.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, h.2 ha, rfl, rfl⟩
#align simple_graph.subgraph.map_monotone SimpleGraph.Subgraph.map_monotone

theorem map_sup {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G') {H H' : G.Subgraph} :
    (H ⊔ H').map f = H.map f ⊔ H'.map f := by
  ext1
  · simp only [Set.image_union, map_verts, verts_sup]
  · ext
    simp only [Relation.Map, map_adj, sup_adj]
    constructor
    · rintro ⟨a, b, h | h, rfl, rfl⟩
      · exact Or.inl ⟨_, _, h, rfl, rfl⟩
      · exact Or.inr ⟨_, _, h, rfl, rfl⟩
    · rintro (⟨a, b, h, rfl, rfl⟩ | ⟨a, b, h, rfl, rfl⟩)
      · exact ⟨_, _, Or.inl h, rfl, rfl⟩
      · exact ⟨_, _, Or.inr h, rfl, rfl⟩
#align simple_graph.subgraph.map_sup SimpleGraph.Subgraph.map_sup

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
protected def comap {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) : G.Subgraph where
  verts := f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm _ _ h := ⟨G.symm h.1, H.symm h.2⟩
#align simple_graph.subgraph.comap SimpleGraph.Subgraph.comap

theorem comap_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp (config := { contextual := true }) only [comap_adj, and_imp, true_and_iff]
    intro
    apply h.2
#align simple_graph.subgraph.comap_monotone SimpleGraph.Subgraph.comap_monotone

theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (H' : G'.Subgraph) :
    H.map f ≤ H' ↔ H ≤ H'.comap f := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, fun v w hvw ↦ ?_⟩, fun h ↦ ⟨fun v ↦ ?_, fun v w ↦ ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and_iff]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro w hw rfl
    exact h.1 hw
  · simp only [Relation.Map, map_adj, forall_exists_index, and_imp]
    rintro u u' hu rfl rfl
    exact (h.2 hu).2
#align simple_graph.subgraph.map_le_iff_le_comap SimpleGraph.Subgraph.map_le_iff_le_comap

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
def inclusion {x y : Subgraph G} (h : x ≤ y) : x.coe →g y.coe where
  toFun v := ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw
#align simple_graph.subgraph.inclusion SimpleGraph.Subgraph.inclusion

theorem inclusion.injective {x y : Subgraph G} (h : x ≤ y) : Function.Injective (inclusion h) := by
  intro v w h
  rw [inclusion, DFunLike.coe, Subtype.mk_eq_mk] at h
  exact Subtype.ext h
#align simple_graph.subgraph.inclusion.injective SimpleGraph.Subgraph.inclusion.injective

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
protected def hom (x : Subgraph G) : x.coe →g G where
  toFun v := v
  map_rel' := x.adj_sub
#align simple_graph.subgraph.hom SimpleGraph.Subgraph.hom

@[simp] lemma coe_hom (x : Subgraph G) :
    (x.hom : x.verts → V) = (fun (v : x.verts) => (v : V)) := rfl

theorem hom.injective {x : Subgraph G} : Function.Injective x.hom :=
  fun _ _ ↦ Subtype.ext
#align simple_graph.subgraph.hom.injective SimpleGraph.Subgraph.hom.injective

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
def spanningHom (x : Subgraph G) : x.spanningCoe →g G where
  toFun := id
  map_rel' := x.adj_sub
#align simple_graph.subgraph.spanning_hom SimpleGraph.Subgraph.spanningHom

theorem spanningHom.injective {x : Subgraph G} : Function.Injective x.spanningHom :=
  fun _ _ ↦ id
#align simple_graph.subgraph.spanning_hom.injective SimpleGraph.Subgraph.spanningHom.injective

theorem neighborSet_subset_of_subgraph {x y : Subgraph G} (h : x ≤ y) (v : V) :
    x.neighborSet v ⊆ y.neighborSet v :=
  fun _ h' ↦ h.2 h'
#align simple_graph.subgraph.neighbor_set_subset_of_subgraph SimpleGraph.Subgraph.neighborSet_subset_of_subgraph

instance neighborSet.decidablePred (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· ∈ G'.neighborSet v) :=
  h v
#align simple_graph.subgraph.neighbor_set.decidable_pred SimpleGraph.Subgraph.neighborSet.decidablePred

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)
#align simple_graph.subgraph.finite_at SimpleGraph.Subgraph.finiteAt

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' ≤ G'') (v : G'.verts)
    [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)
#align simple_graph.subgraph.finite_at_of_subgraph SimpleGraph.Subgraph.finiteAtOfSubgraph

instance (G' : Subgraph G) [Fintype G'.verts] (v : V) [DecidablePred (· ∈ G'.neighborSet v)] :
    Fintype (G'.neighborSet v) :=
  Set.fintypeSubset G'.verts (neighborSet_subset_verts G' v)

instance coeFiniteAt {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)] :
    Fintype (G'.coe.neighborSet v) :=
  Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm
#align simple_graph.subgraph.coe_finite_at SimpleGraph.Subgraph.coeFiniteAt

theorem IsSpanning.card_verts [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning) :
    G'.verts.toFinset.card = Fintype.card V := by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr
#align simple_graph.subgraph.is_spanning.card_verts SimpleGraph.Subgraph.IsSpanning.card_verts

/-- The degree of a vertex in a subgraph. It's zero for vertices outside the subgraph. -/
def degree (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] : ℕ :=
  Fintype.card (G'.neighborSet v)
#align simple_graph.subgraph.degree SimpleGraph.Subgraph.degree

theorem finset_card_neighborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    (G'.neighborSet v).toFinset.card = G'.degree v := by
  rw [degree, Set.toFinset_card]
#align simple_graph.subgraph.finset_card_neighbor_set_eq_degree SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree

theorem degree_le (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G.neighborSet v)] : G'.degree v ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)
#align simple_graph.subgraph.degree_le SimpleGraph.Subgraph.degree_le

theorem degree_le' (G' G'' : Subgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G''.neighborSet v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_card (neighborSet_subset_of_subgraph h v)
#align simple_graph.subgraph.degree_le' SimpleGraph.Subgraph.degree_le'

@[simp]
theorem coe_degree (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
    [Fintype (G'.neighborSet v)] : G'.coe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)
#align simple_graph.subgraph.coe_degree SimpleGraph.Subgraph.coe_degree

@[simp]
theorem degree_spanningCoe {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree, Subgraph.degree]
  congr!
#align simple_graph.subgraph.degree_spanning_coe SimpleGraph.Subgraph.degree_spanningCoe

theorem degree_eq_one_iff_unique_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    G'.degree v = 1 ↔ ∃! w : V, G'.Adj v w := by
  rw [← finset_card_neighborSet_eq_degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]
#align simple_graph.subgraph.degree_eq_one_iff_unique_adj SimpleGraph.Subgraph.degree_eq_one_iff_unique_adj

end Subgraph

section MkProperties

/-! ### Properties of `singletonSubgraph` and `subgraphOfAdj` -/


variable {G : SimpleGraph V} {G' : SimpleGraph W}

instance nonempty_singletonSubgraph_verts (v : V) : Nonempty (G.singletonSubgraph v).verts :=
  ⟨⟨v, Set.mem_singleton v⟩⟩
#align simple_graph.nonempty_singleton_subgraph_verts SimpleGraph.nonempty_singletonSubgraph_verts

@[simp]
theorem singletonSubgraph_le_iff (v : V) (H : G.Subgraph) :
    G.singletonSubgraph v ≤ H ↔ v ∈ H.verts := by
  refine ⟨fun h ↦ h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ ↦ False.elim
#align simple_graph.singleton_subgraph_le_iff SimpleGraph.singletonSubgraph_le_iff

@[simp]
theorem map_singletonSubgraph (f : G →g G') {v : V} :
    Subgraph.map f (G.singletonSubgraph v) = G'.singletonSubgraph (f v) := by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, IsEmpty.forall_iff, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim
#align simple_graph.map_singleton_subgraph SimpleGraph.map_singletonSubgraph

@[simp]
theorem neighborSet_singletonSubgraph (v w : V) : (G.singletonSubgraph v).neighborSet w = ∅ :=
  rfl
#align simple_graph.neighbor_set_singleton_subgraph SimpleGraph.neighborSet_singletonSubgraph

@[simp]
theorem edgeSet_singletonSubgraph (v : V) : (G.singletonSubgraph v).edgeSet = ∅ :=
  Sym2.fromRel_bot
#align simple_graph.edge_set_singleton_subgraph SimpleGraph.edgeSet_singletonSubgraph

theorem eq_singletonSubgraph_iff_verts_eq (H : G.Subgraph) {v : V} :
    H = G.singletonSubgraph v ↔ H.verts = {v} := by
  refine ⟨fun h ↦ by rw [h, singletonSubgraph_verts], fun h ↦ ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false_iff]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h, Set.mem_singleton_iff] at ha1 ha2
    subst_vars
    exact ha.ne rfl
#align simple_graph.eq_singleton_subgraph_iff_verts_eq SimpleGraph.eq_singletonSubgraph_iff_verts_eq

instance nonempty_subgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) :
    Nonempty (G.subgraphOfAdj hvw).verts :=
  ⟨⟨v, by simp⟩⟩
#align simple_graph.nonempty_subgraph_of_adj_verts SimpleGraph.nonempty_subgraphOfAdj_verts

@[simp]
theorem edgeSet_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).edgeSet = {s(v, w)} := by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj, iff_self_iff,
    forall₂_true_iff]
#align simple_graph.edge_set_subgraph_of_adj SimpleGraph.edgeSet_subgraphOfAdj

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
#align simple_graph.subgraph_of_adj_symm SimpleGraph.subgraphOfAdj_symm

@[simp]
theorem map_subgraphOfAdj (f : G →g G') {v w : V} (hvw : G.Adj v w) :
    Subgraph.map f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f.map_adj hvw) := by
  ext
  · simp only [Subgraph.map_verts, subgraphOfAdj_verts, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl | rfl, rfl⟩ <;> simp
    · rintro (rfl | rfl)
      · use v
        simp
      · use w
        simp
  · simp only [Relation.Map, Subgraph.map_adj, subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff]
    constructor
    · rintro ⟨a, b, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl, rfl⟩ <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · use v, w
        simp
      · use w, v
        simp
#align simple_graph.map_subgraph_of_adj SimpleGraph.map_subgraphOfAdj

theorem neighborSet_subgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u ⊆ {v, w} :=
  (G.subgraphOfAdj hvw).neighborSet_subset_verts _
#align simple_graph.neighbor_set_subgraph_of_adj_subset SimpleGraph.neighborSet_subgraphOfAdj_subset

@[simp]
theorem neighborSet_fst_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet v = {w} := by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]
#align simple_graph.neighbor_set_fst_subgraph_of_adj SimpleGraph.neighborSet_fst_subgraphOfAdj

@[simp]
theorem neighborSet_snd_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet w = {v} := by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm
#align simple_graph.neighbor_set_snd_subgraph_of_adj SimpleGraph.neighborSet_snd_subgraphOfAdj

@[simp]
theorem neighborSet_subgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u ≠ v)
    (hw : u ≠ w) : (G.subgraphOfAdj hvw).neighborSet u = ∅ := by
  ext
  simp [hv.symm, hw.symm]
#align simple_graph.neighbor_set_subgraph_of_adj_of_ne_of_ne SimpleGraph.neighborSet_subgraphOfAdj_of_ne_of_ne

theorem neighborSet_subgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u =
    (if u = v then {w} else ∅) ∪ if u = w then {v} else ∅ := by
  split_ifs <;> subst_vars <;> simp [*, Set.singleton_def]
#align simple_graph.neighbor_set_subgraph_of_adj SimpleGraph.neighborSet_subgraphOfAdj

theorem singletonSubgraph_fst_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph u ≤ G.subgraphOfAdj h := by
  simp
#align simple_graph.singleton_subgraph_fst_le_subgraph_of_adj SimpleGraph.singletonSubgraph_fst_le_subgraphOfAdj

theorem singletonSubgraph_snd_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph v ≤ G.subgraphOfAdj h := by
  simp
#align simple_graph.singleton_subgraph_snd_le_subgraph_of_adj SimpleGraph.singletonSubgraph_snd_le_subgraphOfAdj

end MkProperties

namespace Subgraph

variable {G : SimpleGraph V}

/-! ### Subgraphs of subgraphs -/


/-- Given a subgraph of a subgraph of `G`, construct a subgraph of `G`. -/
protected abbrev coeSubgraph {G' : G.Subgraph} : G'.coe.Subgraph → G.Subgraph :=
  Subgraph.map G'.hom
#align simple_graph.subgraph.coe_subgraph SimpleGraph.Subgraph.coeSubgraph

/-- Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
protected abbrev restrict {G' : G.Subgraph} : G.Subgraph → G'.coe.Subgraph :=
  Subgraph.comap G'.hom
#align simple_graph.subgraph.restrict SimpleGraph.Subgraph.restrict

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
#align simple_graph.subgraph.restrict_coe_subgraph SimpleGraph.Subgraph.restrict_coeSubgraph

theorem coeSubgraph_injective (G' : G.Subgraph) :
    Function.Injective (Subgraph.coeSubgraph : G'.coe.Subgraph → G.Subgraph) :=
  Function.LeftInverse.injective restrict_coeSubgraph
#align simple_graph.subgraph.coe_subgraph_injective SimpleGraph.Subgraph.coeSubgraph_injective

lemma coeSubgraph_le {H : G.Subgraph} (H' : H.coe.Subgraph) :
    Subgraph.coeSubgraph H' ≤ H := by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

lemma coeSubgraph_restrict_eq {H : G.Subgraph} (H' : G.Subgraph) :
    Subgraph.coeSubgraph (H.restrict H') = H ⊓ H' := by
  ext
  · simp [and_comm]
  · simp_rw [coeSubgraph_adj, restrict_adj]
    simp only [exists_and_left, exists_prop, ge_iff_le, inf_adj, and_congr_right_iff]
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
#align simple_graph.subgraph.delete_edges SimpleGraph.Subgraph.deleteEdges

section DeleteEdges

variable {G' : G.Subgraph} (s : Set (Sym2 V))

@[simp]
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl
#align simple_graph.subgraph.delete_edges_verts SimpleGraph.Subgraph.deleteEdges_verts

@[simp]
theorem deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ ¬s(v, w) ∈ s :=
  Iff.rfl
#align simple_graph.subgraph.delete_edges_adj SimpleGraph.Subgraph.deleteEdges_adj

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext <;> simp [and_assoc, not_or]
#align simple_graph.subgraph.delete_edges_delete_edges SimpleGraph.Subgraph.deleteEdges_deleteEdges

@[simp]
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp
#align simple_graph.subgraph.delete_edges_empty_eq SimpleGraph.Subgraph.deleteEdges_empty_eq

@[simp]
theorem deleteEdges_spanningCoe_eq :
    G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp
#align simple_graph.subgraph.delete_edges_spanning_coe_eq SimpleGraph.Subgraph.deleteEdges_spanningCoe_eq

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
    simp only [Sym2.map_pair_eq, Sym2.eq]
    contrapose!
    rintro (_ | _) <;> simpa only [Sym2.eq_swap]
  · intro h' hs
    exact h' _ hs rfl
#align simple_graph.subgraph.delete_edges_coe_eq SimpleGraph.Subgraph.deleteEdges_coe_eq

theorem coe_deleteEdges_eq (s : Set (Sym2 V)) :
    (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map (↑) ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp
#align simple_graph.subgraph.coe_delete_edges_eq SimpleGraph.Subgraph.coe_deleteEdges_eq

theorem deleteEdges_le : G'.deleteEdges s ≤ G' := by
  constructor <;> simp (config := { contextual := true }) [subset_rfl]
#align simple_graph.subgraph.delete_edges_le SimpleGraph.Subgraph.deleteEdges_le

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;> simp (config := { contextual := true }) only [deleteEdges_verts, deleteEdges_adj,
    true_and_iff, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs ↦ hs' (h hs)
#align simple_graph.subgraph.delete_edges_le_of_le SimpleGraph.Subgraph.deleteEdges_le_of_le

@[simp]
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp (config := { contextual := true }) [imp_false]
#align simple_graph.subgraph.delete_edges_inter_edge_set_left_eq SimpleGraph.Subgraph.deleteEdges_inter_edgeSet_left_eq

@[simp]
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp (config := { contextual := true }) [imp_false]
#align simple_graph.subgraph.delete_edges_inter_edge_set_right_eq SimpleGraph.Subgraph.deleteEdges_inter_edgeSet_right_eq

theorem coe_deleteEdges_le : (G'.deleteEdges s).coe ≤ (G'.coe : SimpleGraph G'.verts) := by
  intro v w
  simp (config := { contextual := true })
#align simple_graph.subgraph.coe_delete_edges_le SimpleGraph.Subgraph.coe_deleteEdges_le

theorem spanningCoe_deleteEdges_le (G' : G.Subgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe ≤ G'.spanningCoe :=
  spanningCoe_le_of_le (deleteEdges_le s)
#align simple_graph.subgraph.spanning_coe_delete_edges_le SimpleGraph.Subgraph.spanningCoe_deleteEdges_le

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
#align simple_graph.subgraph.induce SimpleGraph.Subgraph.induce

theorem _root_.SimpleGraph.induce_eq_coe_induce_top (s : Set V) :
    G.induce s = ((⊤ : G.Subgraph).induce s).coe := by
  ext
  simp
#align simple_graph.induce_eq_coe_induce_top SimpleGraph.induce_eq_coe_induce_top

section Induce

variable {G' G'' : G.Subgraph} {s s' : Set V}

theorem induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' := by
  constructor
  · simp [hs]
  · simp (config := { contextual := true }) only [induce_adj, true_and_iff, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩
#align simple_graph.subgraph.induce_mono SimpleGraph.Subgraph.induce_mono

@[mono]
theorem induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s :=
  induce_mono hg subset_rfl
#align simple_graph.subgraph.induce_mono_left SimpleGraph.Subgraph.induce_mono_left

@[mono]
theorem induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' :=
  induce_mono le_rfl hs
#align simple_graph.subgraph.induce_mono_right SimpleGraph.Subgraph.induce_mono_right

@[simp]
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp
#align simple_graph.subgraph.induce_empty SimpleGraph.Subgraph.induce_empty

@[simp]
theorem induce_self_verts : G'.induce G'.verts = G' := by
  ext
  · simp
  · constructor <;>
      simp (config := { contextual := true }) only [induce_adj, imp_true_iff, and_true_iff]
    exact fun ha ↦ ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩
#align simple_graph.subgraph.induce_self_verts SimpleGraph.Subgraph.induce_self_verts

lemma le_induce_top_verts : G' ≤ (⊤ : G.Subgraph).induce G'.verts :=
  calc G' = G'.induce G'.verts               := Subgraph.induce_self_verts.symm
       _  ≤ (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top

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
  ext <;> simp (config := { contextual := true }) [-Set.bot_eq_empty, Prop.bot_eq_false]
#align simple_graph.subgraph.singleton_subgraph_eq_induce SimpleGraph.Subgraph.singletonSubgraph_eq_induce

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
      obtain ⟨rfl | rfl, rfl | rfl, ha⟩ := h <;> first |exact (ha.ne rfl).elim|simp
#align simple_graph.subgraph.subgraph_of_adj_eq_induce SimpleGraph.Subgraph.subgraphOfAdj_eq_induce

end Induce

/-- Given a subgraph and a set of vertices, delete all the vertices from the subgraph,
if present. Any edges incident to the deleted vertices are deleted as well. -/
abbrev deleteVerts (G' : G.Subgraph) (s : Set V) : G.Subgraph :=
  G'.induce (G'.verts \ s)
#align simple_graph.subgraph.delete_verts SimpleGraph.Subgraph.deleteVerts

section DeleteVerts

variable {G' : G.Subgraph} {s : Set V}

theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl
#align simple_graph.subgraph.delete_verts_verts SimpleGraph.Subgraph.deleteVerts_verts

theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ ¬u ∈ s ∧ v ∈ G'.verts ∧ ¬v ∈ s ∧ G'.Adj u v := by
  simp [and_assoc]
#align simple_graph.subgraph.delete_verts_adj SimpleGraph.Subgraph.deleteVerts_adj

@[simp]
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s ∪ s') := by
  ext <;> simp (config := { contextual := true }) [not_or, and_assoc]
#align simple_graph.subgraph.delete_verts_delete_verts SimpleGraph.Subgraph.deleteVerts_deleteVerts

@[simp]
theorem deleteVerts_empty : G'.deleteVerts ∅ = G' := by
  simp [deleteVerts]
#align simple_graph.subgraph.delete_verts_empty SimpleGraph.Subgraph.deleteVerts_empty

theorem deleteVerts_le : G'.deleteVerts s ≤ G' := by
  constructor <;> simp [Set.diff_subset]
#align simple_graph.subgraph.delete_verts_le SimpleGraph.Subgraph.deleteVerts_le

@[mono]
theorem deleteVerts_mono {G' G'' : G.Subgraph} (h : G' ≤ G'') :
    G'.deleteVerts s ≤ G''.deleteVerts s :=
  induce_mono h (Set.diff_subset_diff_left h.1)
#align simple_graph.subgraph.delete_verts_mono SimpleGraph.Subgraph.deleteVerts_mono

@[mono]
theorem deleteVerts_anti {s s' : Set V} (h : s ⊆ s') : G'.deleteVerts s' ≤ G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.diff_subset_diff_right h)
#align simple_graph.subgraph.delete_verts_anti SimpleGraph.Subgraph.deleteVerts_anti

@[simp]
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts ∩ s) = G'.deleteVerts s := by
  ext <;> simp (config := { contextual := true }) [imp_false]
#align simple_graph.subgraph.delete_verts_inter_verts_left_eq SimpleGraph.Subgraph.deleteVerts_inter_verts_left_eq

@[simp]
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s ∩ G'.verts) = G'.deleteVerts s := by
  ext <;> simp (config := { contextual := true }) [imp_false]
#align simple_graph.subgraph.delete_verts_inter_verts_set_right_eq SimpleGraph.Subgraph.deleteVerts_inter_verts_set_right_eq

end DeleteVerts

end Subgraph

end SimpleGraph
