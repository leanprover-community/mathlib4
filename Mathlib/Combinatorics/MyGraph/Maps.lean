/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller
-/
import Mathlib.Combinatorics.MyGraph.Dart
import Mathlib.Data.FunLike.Fintype
import Mathlib.Logic.Embedding.Set

/-!
# Maps between graphs

This file defines two functions and three structures relating graphs.
The structures directly correspond to the classification of functions as
injective, surjective and bijective, and have corresponding notation.

## Main definitions

* `MyGraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `MyGraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `MyGraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `MyGraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `MyGraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `MyGraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `MyGraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/


open Function

namespace MyGraph

variable {V W X : Type*} (G : MyGraph V) (G' : MyGraph W) {u v : V}

/-! ## Map and comap -/


protected def map (f : V ↪ W) (G : MyGraph V) : MyGraph W where
  verts := f '' G.verts
  Adj := Relation.Map G.Adj f f
  edge_vert h := by
    obtain ⟨x, b, h1, h2, _⟩ := h
    use x, G.edge_vert h1, h2
  symm a b := by
    rintro ⟨v, w, h, rfl, rfl⟩
    use w, v, h.symm, rfl
  loopless a := by
    rintro ⟨v, w, h, rfl, h'⟩
    exact h.ne (f.injective h'.symm)


instance instDecidableMapAdj {f : V ↪ W} {a b} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) := ‹Decidable (Relation.Map G.Adj f f a b)›


@[simp]
theorem map_adj (f : V ↪ W) (G : MyGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

@[simp]
theorem map_verts (f : V ↪ W) (G : MyGraph V) : (G.map f).verts = f '' G.verts := rfl

lemma map_adj_apply {G : MyGraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp

theorem map_monotone (f : V ↪ W) : Monotone (MyGraph.map f) := by
  rintro G G' h
  constructor
  · intro v ⟨w, hw⟩
    use w, h.1 hw.1, hw.2
  · simp only [map_adj, forall_exists_index, and_imp]
    intro v w x y h' h1 h2
    use x, y, h.2 h'

@[simp]
lemma map_id : G.map (Function.Embedding.refl _) = G :=
  MyGraph.ext (by ext; simp) (Relation.map_id_id _)


variable {X : Type*}
@[simp] lemma map_map (f : V ↪ W) (g : W ↪ X) : (G.map f).map g = G.map (f.trans g) :=
  MyGraph.ext (by ext; simp) <| Relation.map_map _ _ _ _ _

protected def comap (f : V → W) (G : MyGraph W) : MyGraph V where
  verts := f ⁻¹' G.verts
  Adj u v := G.Adj (f u) (f v)
  edge_vert h := G.edge_vert h
  symm _ _ h := h.symm
  loopless _ := G.loopless _

@[simp] lemma comap_adj {u v : V} {G : MyGraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl


@[simp]
theorem comap_verts (f : V ↪ W) (G : MyGraph W) : (G.comap f).verts = f ⁻¹' G.verts := rfl


@[simp] lemma comap_id {G : MyGraph V} : G.comap id = G := MyGraph.ext rfl rfl

@[simp] lemma comap_comap {G : MyGraph X} (f : V → W) (g : W → X) :
  (G.comap g).comap f = G.comap (g ∘ f) := rfl

instance instDecidableComapAdj (f : V → W) (G : MyGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _

lemma comap_symm (G : MyGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext a b
  · simp only [Equiv.coe_toEmbedding,  map_verts, Set.mem_image_equiv]
    tauto
  · simp only [Equiv.coe_toEmbedding, comap_adj, map_adj]
    constructor <;> intro h
    · use e.symm a, e.symm b
      simpa
    · obtain ⟨_, _, _, rfl, rfl⟩ := h
      simpa

lemma map_symm (G : MyGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]

theorem comap_monotone (f : V ↪ W) : Monotone (MyGraph.comap f) := by
  intro G G' h
  constructor
  · simp only [comap_verts]
    intro w hw
    exact h.1 hw
  · simp only [comap_adj]
    intro v w hw
    exact h.2 hw

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : MyGraph V) : (G.map f).comap f = G := by
  ext <;> simp


theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (MyGraph.comap f) (MyGraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (MyGraph.map f) :=
  (leftInverse_comap_map f).injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (MyGraph.comap f) :=
  (leftInverse_comap_map f).surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : MyGraph V) (G' : MyGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f := by
  constructor <;> intro h
  · constructor
    · intro v hv
      apply h.1
      simpa using hv
    · intro v w h'
      apply h.2
      simpa using h'
  · constructor
    · intro v hv
      simp only [map_verts, Set.mem_image] at *
      obtain ⟨u, hu, rfl⟩ := hv
      apply h.1 hu
    · intro v w h'
      simp only [map_adj] at *
      obtain ⟨u, v, h1, rfl, rfl⟩ := h'
      apply h.2 h1

theorem map_comap_le (f : V ↪ W) (G : MyGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

-- lemma le_comap_of_subsingleton (f : V → W) [Subsingleton V] : G ≤ G'.comap f := by
--   intros v w; simp [Subsingleton.elim v w]

-- lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f ≤ G' := by
--   rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

/-- Given a family of vertex types indexed by `ι`, pulling back from `⊤ : MyGraph ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal. -/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : MyGraph (Σ i, V i) :=
  MyGraph.comap Sigma.fst ⊤

/-- Equivalent types have equivalent simple graphs. -/
@[simps apply]
protected def _root_.Equiv.MyGraph (e : V ≃ W) : MyGraph V ≃ MyGraph W where
  toFun := MyGraph.comap e.symm
  invFun := MyGraph.comap e
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma _root_.Equiv.MyGraph_refl : (Equiv.refl V).MyGraph = Equiv.refl _ := by
  ext <;> rfl

@[simp] lemma _root_.Equiv.MyGraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
  (e₁.trans e₂).MyGraph = e₁.MyGraph.trans e₂.MyGraph := rfl

@[simp]
lemma _root_.Equiv.symm_MyGraph (e : V ≃ W) : e.MyGraph.symm = e.symm.MyGraph := rfl


/--
Given a graph on a set of vertices, we can make it a spanning `MyGraph V` by
adding in the remaining vertices without adding in any additional edges.
-/
@[simp]
abbrev spanningCoe (G : MyGraph V) : MyGraph V := (G.induce Set.univ)

lemma spanningCoe_eq_induce_univ (G : MyGraph V) : G.spanningCoe = (G.induce Set.univ) := rfl

theorem spanningCoe_eq_self {G : MyGraph V} (h : G.IsSpanning) : G.spanningCoe = G := by
  rw [spanningCoe_eq_induce_univ, isSpanning_iff] at *
  exact h ▸ G.induce_self_verts

-- theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
--   map_comap_le _ _


/-! ## Homomorphisms, embeddings and isomorphisms -/


/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G'.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj

/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} {G₁ G₂ : MyGraph V} {H : MyGraph W} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
protected abbrev id : G →g G :=
  RelHom.id _

@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G →g G) = id := rfl

instance [Subsingleton (V → W)] : Subsingleton (G →g H) := DFunLike.coe_injective.subsingleton

instance [IsEmpty V] : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

instance [Finite V] [Finite W] : Finite (G →g H) := DFunLike.finite _

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h

theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h

theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def ofLE (h : G₁ ≤ G₂) : G₁ →g G₂ := ⟨id, @h.2⟩

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE h) = id := rfl

lemma ofLE_apply (h : G₁ ≤ G₂) (v : V) : ofLE h v = v := rfl

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[deprecated ofLE (since := "2025-03-17")]
def mapSpanningSubgraphs {G G' : MyGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h.2 ha

@[deprecated "This is true by simp" (since := "2025-03-17")]
lemma mapSpanningSubgraphs_inj {G G' : MyGraph V} {v w : V} (h : G ≤ G') :
    ofLE h v = ofLE h w ↔ v = w := by simp

@[deprecated "This is true by simp" (since := "2025-03-17")]
lemma mapSpanningSubgraphs_injective {G G' : MyGraph V} (h : G ≤ G') :
    Injective (ofLE h) :=
  fun v w hvw ↦ by simpa using hvw

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

/-- Every graph homomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : MyGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ (top_adj.mpr h))

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `MyGraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : MyGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

variable {G'' : MyGraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Hom

namespace Embedding

variable {G G'} {H : MyGraph W} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom

@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl

@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : MyGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem comap_apply (f : V ↪ W) (G : MyGraph W) (v : V) :
    MyGraph.Embedding.comap f G v = f v := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- Porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : MyGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem map_apply (f : V ↪ W) (G : MyGraph V) (v : V) :
    MyGraph.Embedding.map f G v = f v := rfl


/- Induced graphs embed in the original graph.

-- Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
-- complete graph. -/
-- protected abbrev induce (s : Set V) : G.induce s ↪g G :=
--   MyGraph.Embedding.comap (Function.Embedding.refl _)  G

-- /- Graphs on a set of vertices embed in their `spanningCoe`. -/
-- protected abbrev spanningCoe {s : Set V} (G : MyGraph s) : G ↪g G.spanningCoe :=
--   MyGraph.Embedding.map (Function.Embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ↪ β) :
    (⊤ : MyGraph α) ↪g (⊤ : MyGraph β) :=
  { f with map_rel_iff' := by simp }

@[simp] lemma coe_completeGraph {α β : Type*} (f : α ↪ β) : ⇑(Embedding.completeGraph f) = f := rfl

variable {G'' : MyGraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

-- /-- Graph embeddings from `G` to `H` are the same thing as graph embeddings from `Gᶜ` to `Hᶜ`. -/
-- def complEquiv : G ↪g H ≃ Gᶜ ↪g Hᶜ where
--   toFun f := ⟨f.toEmbedding, by simp⟩
--   invFun f := ⟨f.toEmbedding, fun {v w} ↦ by
--     obtain rfl | hvw := eq_or_ne v w
--     · simp
--     · simpa [hvw, not_iff_not] using f.map_adj_iff (v := v) (w := w)⟩
--   left_inv f := rfl
--   right_inv f := rfl

end Embedding

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _


/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  RelIso.symm f

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f

@[simp]
theorem symm_toHom_comp_toHom : f.symm.toHom.comp f.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]

@[simp]
theorem toHom_comp_symm_toHom : f.toHom.comp f.symm.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet where
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

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp


include f in
theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert rfl

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : MyGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma comap_apply (f : V ≃ W) (G : MyGraph W) (v : V) :
    MyGraph.Iso.comap f G v = f v := rfl

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : MyGraph W) (w : W) :
    (MyGraph.Iso.comap f G).symm w = f.symm w := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : MyGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma map_apply (f : V ≃ W) (G : MyGraph V) (v : V) :
    MyGraph.Iso.map f G v = f v := rfl

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : MyGraph V) (w : W) :
    (MyGraph.Iso.map f G).symm w = f.symm w := rfl

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ≃ β) :
    (⊤ : MyGraph α) ≃g (⊤ : MyGraph β) :=
  { f with map_rel_iff' := by simp }

theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

variable {G'' : MyGraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Iso

--
-- /- The graph induced on `Set.univ` is isomorphic to the original graph. -/
-- @[simps!]
-- def induceUnivIso (G : MyGraph V) : G.induce Set.univ ≃g G where
--   toEquiv := Equiv.Set.univ V
--   map_rel_iff' :=
--by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
--                                 Subtype.forall, Set.mem_univ, forall_true_left, implies_true]

section Finite

variable [Fintype V] {n : ℕ}

/-- Given a graph over a finite vertex type `V` and a proof `hc` that `Fintype.card V = n`,
`G.overFin n` is an isomorphic (as shown in `overFinIso`) graph over `Fin n`. -/
def overFin (hc : Fintype.card V = n) : MyGraph (Fin n) where
  verts := Set.univ
  Adj x y := G.Adj ((Fintype.equivFinOfCardEq hc).symm x) ((Fintype.equivFinOfCardEq hc).symm y)
  edge_vert _ := by trivial
  symm x y := by simp_rw [adj_comm, imp_self]
  loopless := fun _ h ↦ G.loopless _ h

/-- The isomorphism between `G` and `G.overFin hc`. -/
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc := by
  use Fintype.equivFinOfCardEq hc; simp [overFin]

end Finite





end MyGraph
