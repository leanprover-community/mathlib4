/-
Copyright (c) 2025 Jaafar Tanoukhi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.Logic.Embedding.Set

/-!
# Maps between graphs

## Main definitions

* `Digraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `Digraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `Digraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `Digraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `Digraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `Digraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `Digraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/


open Function

namespace Digraph

variable {V W X : Type*} (G : Digraph V) (G' : Digraph W) {u v : V}

/-! ## Map and comap -/


/-- Given an injective function, there is a covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `Digraph.map_injective`). -/
protected def map (f : V ↪ W) (G : Digraph V) : Digraph W where
  Adj := Relation.Map G.Adj f f

instance instDecidableMapAdj {f : V ↪ W} {a b} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) := ‹Decidable (Relation.Map G.Adj f f a b)›

@[simp]
theorem map_adj (f : V ↪ W) (G : Digraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

lemma map_adj_apply {G : Digraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp

theorem map_monotone (f : V ↪ W) : Monotone (Digraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩

@[simp] lemma map_id : G.map (Function.Embedding.refl _) = G :=
  Digraph.ext <| Relation.map_id_id _

@[simp] lemma map_map (f : V ↪ W) (g : W ↪ X) : (G.map f).map g = G.map (f.trans g) :=
  Digraph.ext <| Relation.map_map _ _ _ _ _

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `Digraph.induce` for a wrapper.

This is surjective when `f` is injective (see `Digraph.comap_surjective`). -/
protected def comap (f : V → W) (G : Digraph W) : Digraph V where
  Adj u v := G.Adj (f u) (f v)

@[simp] lemma comap_adj {G : Digraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl

@[simp] lemma comap_id {G : Digraph V} : G.comap id = G := Digraph.ext rfl

@[simp] lemma comap_comap {G : Digraph X} (f : V → W) (g : W → X) :
    (G.comap g).comap f = G.comap (g ∘ f) := rfl

instance instDecidableComapAdj (f : V → W) (G : Digraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _

lemma comap_symm (G : Digraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext; simp only [Equiv.apply_eq_iff_eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]

lemma map_symm (G : Digraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]

theorem comap_monotone (f : V ↪ W) : Monotone (Digraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : Digraph V) : (G.map f).comap f = G := by
  ext
  simp

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (Digraph.comap f) (Digraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (Digraph.map f) :=
  (leftInverse_comap_map f).injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (Digraph.comap f) :=
  (leftInverse_comap_map f).surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : Digraph V) (G' : Digraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h _ _ ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V ↪ W) (G : Digraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

/-- Given a family of vertex types indexed by `ι`, pulling back from `⊤ : Digraph ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal. -/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : Digraph (Σ i, V i) :=
  Digraph.comap Sigma.fst ⊤

/-- Equivalent types have equivalent digraphs. -/
@[simps apply]
protected def _root_.Equiv.Digraph (e : V ≃ W) : Digraph V ≃ Digraph W where
  toFun := Digraph.comap e.symm
  invFun := Digraph.comap e
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma _root_.Equiv.Digraph_refl : (Equiv.refl V).Digraph = Equiv.refl _ := by
  ext; rfl

@[simp] lemma _root_.Equiv.Digraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
    (e₁.trans e₂).Digraph = e₁.Digraph.trans e₂.Digraph := rfl

@[simp]
lemma _root_.Equiv.symm_Digraph (e : V ≃ W) : e.Digraph.symm = e.symm.Digraph := rfl

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `Digraph V` and `Digraph s`.

There is also a notion of induced subgraphs (see `Digraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `Digraph.comap`. -/
abbrev induce (s : Set V) (G : Digraph V) : Digraph s :=
  G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `Digraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `Digraph.map`. -/
abbrev spanningCoe {s : Set V} (G : Digraph s) : Digraph V :=
  G.map (Function.Embedding.subtype _)

theorem induce_spanningCoe {s : Set V} {G : Digraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _

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

variable {G G'} {G₁ G₂ : Digraph V} {H : Digraph W} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
protected abbrev id : G →g G :=
  RelHom.id _

@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G →g G) = id := rfl

instance [Subsingleton (V → W)] : Subsingleton (G →g H) := DFunLike.coe_injective.subsingleton

instance [IsEmpty V] : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def ofLE (h : G₁ ≤ G₂) : G₁ →g G₂ := ⟨id, @h⟩

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE h) = id := rfl

lemma ofLE_apply (h : G₁ ≤ G₂) (v : V) : ofLE h v = v := rfl

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `Digraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

variable {G'' : Digraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Hom


namespace Embedding

variable {G G'} {H : Digraph W} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom

@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl

@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : Digraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem comap_apply (f : V ↪ W) (G : Digraph W) (v : V) :
    Digraph.Embedding.comap f G v = f v := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- Porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : Digraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem map_apply (f : V ↪ W) (G : Digraph V) (v : V) :
    Digraph.Embedding.map f G v = f v := rfl

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
protected abbrev induce (s : Set V) : G.induce s ↪g G :=
  Digraph.Embedding.comap (Function.Embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
protected abbrev spanningCoe {s : Set V} (G : Digraph s) : G ↪g G.spanningCoe :=
  Digraph.Embedding.map (Function.Embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeDigraph {α β : Type*} (f : α ↪ β) : Digraph.completeDigraph α ↪g Digraph.completeDigraph β :=
  { f with map_rel_iff' := by simp }

@[simp] lemma coe_completeGraph {α β : Type*} (f : α ↪ β) :
 ⇑(Embedding.completeDigraph f) = f := rfl

variable {G'' : Digraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Embedding

section induceHom

variable {G G'} {G'' : Digraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def induceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl

@[simp] lemma induceHom_id (G : Digraph V) (s) :
    induceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl

@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl

lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  simpa [Set.MapsTo.restrict_inj]

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

include f in
theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert rfl

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : Digraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma comap_apply (f : V ≃ W) (G : Digraph W) (v : V) :
    Digraph.Iso.comap f G v = f v := rfl

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : Digraph W) (w : W) :
    (Digraph.Iso.comap f G).symm w = f.symm w := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : Digraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma map_apply (f : V ≃ W) (G : Digraph V) (v : V) :
    Digraph.Iso.map f G v = f v := rfl

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : Digraph V) (w : W) :
    (Digraph.Iso.map f G).symm w = f.symm w := rfl

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeDigraph {α β : Type*} (f : α ≃ β) :
  Digraph.completeDigraph α ≃g Digraph.completeDigraph β :=
  { f with map_rel_iff' := by simp }

theorem toEmbedding_completeDigraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeDigraph f).toEmbedding = Embedding.completeDigraph f.toEmbedding :=
  rfl

variable {G'' : Digraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Iso

/-- The graph induced on `Set.univ` is isomorphic to the original graph. -/
@[simps!]
def induceUnivIso (G : Digraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                implies_true]

section Finite

variable [Fintype V] {n : ℕ}

/-- Given a graph over a finite vertex type `V` and a proof `hc` that `Fintype.card V = n`,
`G.overFin n` is an isomorphic (as shown in `overFinIso`) graph over `Fin n`. -/
def overFin (hc : Fintype.card V = n) : Digraph (Fin n) where
  Adj x y := G.Adj ((Fintype.equivFinOfCardEq hc).symm x) ((Fintype.equivFinOfCardEq hc).symm y)

/-- The isomorphism between `G` and `G.overFin hc`. -/
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc := by
  use Fintype.equivFinOfCardEq hc; simp [overFin]

end Finite


end Digraph
