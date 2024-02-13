/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.FunLike.Fintype

/-!
# Maps between graphs

This file defines two functions and three structures relating graphs.
The structures directly correspond to the classification of functions as
injective, surjective and bijective, and have corresponding notation.

## Main definitions

* `SimpleGraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `SimpleGraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `SimpleGraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `SimpleGraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `SimpleGraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `SimpleGraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `SimpleGraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/


open Function

namespace SimpleGraph

variable {V W X : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) {u v : V}

/-! ## Map and comap -/


/-- Given an injective function, there is a covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `SimpleGraph.map_injective`). -/
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Relation.Map G.Adj f f
  symm a b := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, rfl⟩
    use w, v, h.symm, rfl
  loopless a := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, h'⟩
    exact h.ne (f.injective h'.symm)
#align simple_graph.map SimpleGraph.map

instance instDecidableMapAdj {f : V ↪ W} {a b} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) := ‹Decidable (Relation.Map G.Adj f f a b)›
#align simple_graph.decidable_map SimpleGraph.instDecidableMapAdj

@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl
#align simple_graph.map_adj SimpleGraph.map_adj

lemma map_adj_apply {G : SimpleGraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp
#align simple_graph.map_adj_apply SimpleGraph.map_adj_apply

theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩
#align simple_graph.map_monotone SimpleGraph.map_monotone

@[simp] lemma map_id : G.map (Function.Embedding.refl _) = G :=
  SimpleGraph.ext _ _ <| Relation.map_id_id _
#align simple_graph.map_id SimpleGraph.map_id

@[simp] lemma map_map (f : V ↪ W) (g : W ↪ X) : (G.map f).map g = G.map (f.trans g) :=
  SimpleGraph.ext _ _ <| Relation.map_map _ _ _ _ _
#align simple_graph.map_map SimpleGraph.map_map

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`).-/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm _ _ h := h.symm
  loopless _ := G.loopless _
#align simple_graph.comap SimpleGraph.comap

@[simp] lemma comap_adj {G : SimpleGraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl

@[simp] lemma comap_id {G : SimpleGraph V} : G.comap id = G := SimpleGraph.ext _ _ rfl
#align simple_graph.comap_id SimpleGraph.comap_id

@[simp] lemma comap_comap {G : SimpleGraph X} (f : V → W) (g : W → X) :
  (G.comap g).comap f = G.comap (g ∘ f) := rfl
#align simple_graph.comap_comap SimpleGraph.comap_comap

instance instDecidableComapAdj (f : V → W) (G : SimpleGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _

lemma comap_symm (G : SimpleGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext; simp only [Equiv.apply_eq_iff_eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]
#align simple_graph.comap_symm SimpleGraph.comap_symm

lemma map_symm (G : SimpleGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]
#align simple_graph.map_symm SimpleGraph.map_symm

theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha
#align simple_graph.comap_monotone SimpleGraph.comap_monotone

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp
#align simple_graph.comap_map_eq SimpleGraph.comap_map_eq

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f
#align simple_graph.left_inverse_comap_map SimpleGraph.leftInverse_comap_map

theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective
#align simple_graph.map_injective SimpleGraph.map_injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective
#align simple_graph.comap_surjective SimpleGraph.comap_surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩
#align simple_graph.map_le_iff_le_comap SimpleGraph.map_le_iff_le_comap

theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]
#align simple_graph.map_comap_le SimpleGraph.map_comap_le

lemma le_comap_of_subsingleton (f : V → W) [Subsingleton V] : G ≤ G'.comap f := by
  intros v w; simp [Subsingleton.elim v w]

lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f ≤ G' := by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

/-- Given a family of vertex types indexed by `ι`, pulling back from `⊤ : SimpleGraph ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal. -/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst ⊤

/-- Equivalent types have equivalent simple graphs. -/
@[simps apply]
protected def _root_.Equiv.simpleGraph (e : V ≃ W) : SimpleGraph V ≃ SimpleGraph W where
  toFun := SimpleGraph.comap e.symm
  invFun := SimpleGraph.comap e
  left_inv _ := by simp
  right_inv _ := by simp
#align equiv.simple_graph Equiv.simpleGraph

@[simp] lemma _root_.Equiv.simpleGraph_refl : (Equiv.refl V).simpleGraph = Equiv.refl _ := by
  ext; rfl

@[simp] lemma _root_.Equiv.simpleGraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
  (e₁.trans e₂).simpleGraph = e₁.simpleGraph.trans e₂.simpleGraph := rfl
#align equiv.simple_graph_trans Equiv.simpleGraph_trans

@[simp]
lemma _root_.Equiv.symm_simpleGraph (e : V ≃ W) : e.simpleGraph.symm = e.symm.simpleGraph := rfl
#align equiv.symm_simple_graph Equiv.symm_simpleGraph

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `SimpleGraph V` and `SimpleGraph s`.

There is also a notion of induced subgraphs (see `SimpleGraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
#align simple_graph.induce SimpleGraph.induce

@[simp] lemma induce_singleton_eq_top (v : V) : G.induce {v} = ⊤ := by
  rw [eq_top_iff]; apply le_comap_of_subsingleton

/-- Given a graph on a set of vertices, we can make it be a `SimpleGraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `SimpleGraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)
#align simple_graph.spanning_coe SimpleGraph.spanningCoe

theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _
#align simple_graph.induce_spanning_coe SimpleGraph.induce_spanningCoe

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _
#align simple_graph.spanning_coe_induce_le SimpleGraph.spanningCoe_induce_le

/-! ## Homomorphisms, embeddings and isomorphisms -/


/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
#align simple_graph.hom SimpleGraph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
#align simple_graph.embedding SimpleGraph.Embedding

/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj
#align simple_graph.iso SimpleGraph.Iso

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
protected abbrev id : G →g G :=
  RelHom.id _
#align simple_graph.hom.id SimpleGraph.Hom.id

@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G →g G) = id := rfl
#align simple_graph.hom.coe_id SimpleGraph.Hom.coe_id

instance [Subsingleton (V → W)] : Subsingleton (G →g H) := DFunLike.coe_injective.subsingleton

instance [IsEmpty V] : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

instance instFintype [DecidableEq V] [Fintype V] [Fintype W] [DecidableRel G.Adj]
    [DecidableRel H.Adj] : Fintype (G →g H) :=
  Fintype.ofEquiv {f : V → W // ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)}
    { toFun := fun f ↦ ⟨f.1, f.2⟩, invFun := fun f ↦ ⟨f.1, f.2⟩,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance [Finite V] [Finite W] : Finite (G →g H) := DFunLike.finite _

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
#align simple_graph.hom.map_adj SimpleGraph.Hom.map_adj

theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h
#align simple_graph.hom.map_mem_edge_set SimpleGraph.Hom.map_mem_edgeSet

theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h
#align simple_graph.hom.apply_mem_neighbor_set SimpleGraph.Hom.apply_mem_neighborSet

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩
#align simple_graph.hom.map_edge_set SimpleGraph.Hom.mapEdgeSet

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩
#align simple_graph.hom.map_neighbor_set SimpleGraph.Hom.mapNeighborSet

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩
#align simple_graph.hom.map_dart SimpleGraph.Hom.mapDart

@[simp]
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl
#align simple_graph.hom.map_dart_apply SimpleGraph.Hom.mapDart_apply

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha
#align simple_graph.hom.map_spanning_subgraphs SimpleGraph.Hom.mapSpanningSubgraphs

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat' rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj
#align simple_graph.hom.map_edge_set.injective SimpleGraph.Hom.mapEdgeSet.injective

/-- Every graph homomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))
#align simple_graph.hom.injective_of_top_hom SimpleGraph.Hom.injective_of_top_hom

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp
#align simple_graph.hom.comap SimpleGraph.Hom.comap

variable {G'' : SimpleGraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f
#align simple_graph.hom.comp SimpleGraph.Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.hom.coe_comp SimpleGraph.Hom.coe_comp

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def ofLE (h : G₁ ≤ G₂) : G₁ →g G₂ := ⟨id, @h⟩
#align simple_graph.hom.of_le SimpleGraph.Hom.ofLE

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE h) = id := rfl
#align simple_graph.hom.coe_of_le SimpleGraph.Hom.coe_ofLE

end Hom

namespace Embedding

variable {G G'} {H : SimpleGraph W} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _
#align simple_graph.embedding.refl SimpleGraph.Embedding.refl

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom
#align simple_graph.embedding.to_hom SimpleGraph.Embedding.toHom

@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl
#align simple_graph.embedding.coe_to_hom SimpleGraph.Embedding.coe_toHom

@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.embedding.map_adj_iff SimpleGraph.Embedding.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
#align simple_graph.embedding.map_mem_edge_set_iff SimpleGraph.Embedding.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.embedding.apply_mem_neighbor_set_iff SimpleGraph.Embedding.apply_mem_neighborSet_iff

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.injective
#align simple_graph.embedding.map_edge_set SimpleGraph.Embedding.mapEdgeSet

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h
#align simple_graph.embedding.map_neighbor_set SimpleGraph.Embedding.mapNeighborSet

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.comap SimpleGraph.Embedding.comap

@[simp]
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Embedding.comap f G v = f v := rfl
#align simple_graph.embedding.comap_apply SimpleGraph.Embedding.comap_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.map SimpleGraph.Embedding.map

@[simp]
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    SimpleGraph.Embedding.map f G v = f v := rfl
#align simple_graph.embedding.map_apply SimpleGraph.Embedding.map_apply

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G
#align simple_graph.embedding.induce SimpleGraph.Embedding.induce

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G
#align simple_graph.embedding.spanning_coe SimpleGraph.Embedding.spanningCoe

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ↪ β) :
    (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.complete_graph SimpleGraph.Embedding.completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'
#align simple_graph.embedding.comp SimpleGraph.Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.embedding.coe_comp SimpleGraph.Embedding.coe_comp

end Embedding

section induceHom

variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def induceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'
#align simple_graph.induce_hom SimpleGraph.induceHom

@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl
#align simple_graph.coe_induce_hom SimpleGraph.coe_induceHom

@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    induceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl
#align simple_graph.induce_hom_id SimpleGraph.induceHom_id

@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl
#align simple_graph.induce_hom_comp SimpleGraph.induceHom_comp

lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  erw [Set.MapsTo.restrict_inj] <;> assumption

end induceHom

section induceHomLE
variable {s s' : Set V} (h : s ≤ s')

/-- Given an inclusion of vertex subsets, the induced embedding on induced graphs.
This is not an abbreviation for `induceHom` since we get an embedding in this case. -/
def induceHomOfLE (h : s ≤ s') : G.induce s ↪g G.induce s' where
  toEmbedding := Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp

@[simp] lemma induceHomOfLE_apply (v : s) : (G.induceHomOfLE h) v = Set.inclusion h v := rfl

@[simp] lemma induceHomOfLE_toHom :
    (G.induceHomOfLE h).toHom = induceHom (.id : G →g G) ((Set.mapsTo_id s).mono_right h) := by
  ext; simp

end induceHomLE

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _
#align simple_graph.iso.refl SimpleGraph.Iso.refl

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding
#align simple_graph.iso.to_embedding SimpleGraph.Iso.toEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom
#align simple_graph.iso.to_hom SimpleGraph.Iso.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  RelIso.symm f
#align simple_graph.iso.symm SimpleGraph.Iso.symm

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.iso.map_adj_iff SimpleGraph.Iso.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
#align simple_graph.iso.map_mem_edge_set_iff SimpleGraph.Iso.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.iso.apply_mem_neighbor_set_iff SimpleGraph.Iso.apply_mem_neighborSet_iff

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet
    where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Embedding.toFun_eq_coe,
      RelEmbedding.coe_toEmbedding, RelIso.coe_toRelEmbedding, Sym2.map_map, comp_apply,
      Subtype.mk.injEq]
    convert congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Embedding.toFun_eq_coe,
      RelEmbedding.coe_toEmbedding, RelIso.coe_toRelEmbedding, Sym2.map_map, comp_apply,
      Subtype.mk.injEq]
    convert congr_fun Sym2.map_id e
    exact RelIso.apply_symm_apply _ _
#align simple_graph.iso.map_edge_set SimpleGraph.Iso.mapEdgeSet

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp
#align simple_graph.iso.map_neighbor_set SimpleGraph.Iso.mapNeighborSet

theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert rfl
#align simple_graph.iso.card_eq_of_iso SimpleGraph.Iso.card_eq

theorem card_edgeFinset_eq [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    G.edgeFinset.card = G'.edgeFinset.card := by
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset]
  exact f.mapEdgeSet

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.comap SimpleGraph.Iso.comap

@[simp]
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Iso.comap f G v = f v := rfl
#align simple_graph.iso.comap_apply SimpleGraph.Iso.comap_apply

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
    (SimpleGraph.Iso.comap f G).symm w = f.symm w := rfl
#align simple_graph.iso.comap_symm_apply SimpleGraph.Iso.comap_symm_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.map SimpleGraph.Iso.map

@[simp]
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) :
    SimpleGraph.Iso.map f G v = f v := rfl
#align simple_graph.iso.map_apply SimpleGraph.Iso.map_apply

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
    (SimpleGraph.Iso.map f G).symm w = f.symm w := rfl
#align simple_graph.iso.map_symm_apply SimpleGraph.Iso.map_symm_apply

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.complete_graph SimpleGraph.Iso.completeGraph

theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl
#align simple_graph.iso.to_embedding_complete_graph SimpleGraph.Iso.toEmbedding_completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'
#align simple_graph.iso.comp SimpleGraph.Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.iso.coe_comp SimpleGraph.Iso.coe_comp

end Iso

/-- The graph induced on `Set.univ` is isomorphic to the original graph. -/
@[simps!]
def induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                Subtype.forall, Set.mem_univ, forall_true_left, implies_true]

section Finite

variable [Fintype V] {n : ℕ}

/-- Given a graph over a finite vertex type `V` and a proof `hc` that `Fintype.card V = n`,
`G.overFin n` is an isomorphic (as shown in `overFinIso`) graph over `Fin n`. -/
def overFin (hc : Fintype.card V = n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj ((Fintype.equivFinOfCardEq hc).symm x) ((Fintype.equivFinOfCardEq hc).symm y)
  symm x y := by simp_rw [adj_comm, imp_self]

/-- The isomorphism between `G` and `G.overFin hc`. -/
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc := by
  use Fintype.equivFinOfCardEq hc; simp [overFin]

end Finite

end SimpleGraph
