/-
Copyright (c) 2023 Yaël Dillies, Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Finite.Card

/-!
# Copies, containment, and counting of subgraphs

For two simple graphs `G` and `H`, a *(labeled) copy* of `G` in `H` is an injective map from the
vertices of `G` into those of `H` that preserves adjacency, picking out a (not necessarily
induced) subgraph of `H` isomorphic to `G`. An *unlabeled copy* drops the labeling and retains
only the resulting subgraph.

If `H` contains a copy of `G`, we say that `H` *contains* `G`. If the copy is induced (i.e., the
vertex map also *reflects* adjacency), we say that `H` *inducingly contains* `G`.

Throughout, `G` denotes the smaller guest, `H` the larger host, and `I` a third graph for
transitivity, with letters in size order (`G < H < I`) matching the hom direction `G →g H` and
the containment relation `G ⊑ H`. Types are guest-first (`Copy G H`, `Sub G H`, `IsContained G H`,
…) and operations are host-first via dot notation (`H.copyCount G`, `H.subCount G`, …).

## Main declarations

Containment:
* `SimpleGraph.Copy G H` is the type of labeled copies of `G` in `H`, implemented as the subtype
  of *injective* homomorphisms.
* `SimpleGraph.Sub G H` is the type of unlabeled copies of `G` in `H`, implemented as the subtype
  of `SimpleGraph.Subgraph`s of `H` isomorphic to `G`.
* `SimpleGraph.IsContained G H`, `G ⊑ H` is the relation that `H` contains a copy of `G`, that
  is, the type of copies of `G` in `H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to a subgraph of `H`.
  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `H` is `G`-free, that is, `H` does not contain a copy of
  `G`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.
* `SimpleGraph.copyCount H G` is the number of labeled copies of `G` in `H`, i.e. the number of
  injective graph homomorphisms from `G` to `H`.
* `SimpleGraph.subCount H G` is the number of unlabeled copies of `G` in `H`, i.e. the number of
  `SimpleGraph.Subgraph`s of `H` isomorphic to `G`.
* `SimpleGraph.killCopies H G` is a subgraph of `H` that does not contain `G`, obtained by
  arbitrarily removing an edge from each copy of `G` in `H`.

Induced containment:
* Induced copies of `G` inside `H` are already defined as `G ↪g H`.
* `SimpleGraph.IsIndContained G H` is the relation that `G` is contained as an induced subgraph
  in `H`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.IsContained G H`.
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Count induced copies of a graph inside another.
* Make `copyCount`/`subCount` computable (not necessarily efficiently).
* Count the number of graph homomorphisms `G →g H` with `homCount G H`.
* Add densities `copyDensity G H`, `subDensity G H`, and `homDensity G H`.
-/

public section

open Finset Function

namespace SimpleGraph
variable {V V' W W' X : Type*}
  {G G₁ G₂ G₃ : SimpleGraph V} {G' : SimpleGraph V'}
  {H : SimpleGraph W} {H' : SimpleGraph W'}
  {I : SimpleGraph X}

/-!
### Copies

#### Not necessarily induced copies
-/

section Copy

/-- The type of copies as a subtype of *injective* homomorphisms. -/
structure Copy (G : SimpleGraph V) (H : SimpleGraph W) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : G →g H
  injective' : Injective toHom

/-- An injective homomorphism gives rise to a copy. -/
abbrev Hom.toCopy (f : G →g H) (h : Injective f) : Copy G H := .mk f h

/-- An embedding gives rise to a copy. -/
abbrev Embedding.toCopy (f : G ↪g H) : Copy G H := f.toHom.toCopy f.injective

/-- An isomorphism gives rise to a copy. -/
abbrev Iso.toCopy (f : G ≃g H) : Copy G H := f.toEmbedding.toCopy

namespace Copy

instance : FunLike (Copy G H) V W where
  coe f := DFunLike.coe f.toHom
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

lemma injective (f : Copy G H) : Injective f.toHom := f.injective'

@[ext] lemma ext {f g : Copy G H} : (∀ a, f a = g a) → f = g := DFunLike.ext _ _

@[simp] lemma coe_toHom (f : Copy G H) : ⇑f.toHom = f := rfl
@[simp] lemma toHom_apply (f : Copy G H) (a : V) : ⇑f.toHom a = f a := rfl

@[simp] lemma coe_mk (f : G →g H) (hf) : ⇑(.mk f hf : Copy G H) = f := rfl

/-- A copy induces an embedding of edge sets. -/
def mapEdgeSet (f : Copy G H) : G.edgeSet ↪ H.edgeSet where
  toFun := f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A copy induces an embedding of neighbor sets. -/
def mapNeighborSet (f : Copy G H) (a : V) :
    G.neighborSet a ↪ H.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- A copy gives rise to an embedding of vertex types. -/
@[expose] def toEmbedding (f : Copy G H) : V ↪ W := ⟨f, f.injective⟩

@[simp] lemma toEmbedding_apply (f : Copy G H) (a : V) : f.toEmbedding a = f a := rfl

/-- The identity copy from a simple graph to itself. -/
@[expose, refl] def id (G : SimpleGraph V) : Copy G G := ⟨Hom.id, Function.injective_id⟩

@[simp, norm_cast] lemma coe_id : ⇑(id G) = _root_.id := rfl

/-- The composition of copies is a copy. -/
def comp (g : Copy H I) (f : Copy G H) : Copy G I := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]
theorem comp_apply (g : Copy H I) (f : Copy G H) (a : V) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/-- The copy from a subgraph to the supergraph. -/
@[expose] def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) : Copy G₁ G₂ :=
    ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
theorem coe_comp (g : Copy H I) (f : Copy G H) : ⇑(g.comp f) = g ∘ f := by ext; simp

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl

@[simp] theorem ofLE_refl : ofLE G G le_rfl = id G := by ext; simp

@[simp]
theorem ofLE_comp (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ≤ G₃) :
    (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/-- The copy from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G := (Embedding.induce s).toCopy

/-- The copy of `⊥` in any simple graph that can embed its vertices. -/
protected def bot (f : V ↪ W) : Copy (⊥ : SimpleGraph V) H := ⟨⟨f, False.elim⟩, f.injective⟩

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism from a subgraph of `G` to its map under a copy `f : Copy G H`. -/
noncomputable def isoSubgraphMap (f : Copy G H) (G' : G.Subgraph) :
    G'.coe ≃g (G'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- The subgraph of `H` corresponding to a copy of `G` inside `H`. -/
abbrev toSubgraph (f : Copy G H) : H.Subgraph := .map f.toHom ⊤

/-- The isomorphism from `G` to its copy under `f : Copy G H`. -/
noncomputable def isoToSubgraph (f : Copy G H) : G ≃g f.toSubgraph.coe :=
  (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm

@[simp] lemma range_toSubgraph :
    .range (toSubgraph (G := G)) = {H' : H.Subgraph | Nonempty (G ≃g H'.coe)} := by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]

lemma toSubgraph_surjOn :
    Set.SurjOn (toSubgraph (G := G)) .univ {H' : H.Subgraph | Nonempty (G ≃g H'.coe)} :=
  fun H' hH' ↦ by simpa

instance [Subsingleton (V → W)] : Subsingleton (G.Copy H) := DFunLike.coe_injective.subsingleton

instance [Fintype {f : G →g H // Injective f}] : Fintype (G.Copy H) :=
  .ofEquiv {f : G →g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

instance [Finite V] [Finite W] : Finite (G.Copy H) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- A copy of `⊤` gives rise to an embedding of `⊤`. -/
@[expose] def topEmbedding (f : Copy (⊤ : SimpleGraph V) H) : (⊤ : SimpleGraph V) ↪g H :=
  { f.toEmbedding with
    map_rel_iff' := fun {_ _} ↦ ⟨fun h ↦ f.injective.ne_iff.mp h.ne, f.toHom.map_adj⟩ }

@[simp] lemma topEmbedding_apply (f : Copy (⊤ : SimpleGraph V) H) (v : V) :
    f.topEmbedding v = f v := rfl

end Copy

/-- A `G.Subgraph` gives rise to a copy from its coercion to `G`. -/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G := G'.hom.toCopy hom_injective

end Copy

/-!
#### Induced copies

An induced copy of `G` in `H` is an injective map from the vertices of `G` into those of `H`
that *preserves and reflects* adjacency (an edge between two images must come from an edge in
`G`). This is already captured by `G ↪g H`.

### Containment

#### Not necessarily induced containment

`G ⊑ H` (`\squb`).
-/

section IsContained

/-- The relation `IsContained G H`, `G ⊑ H` says that `H` contains a copy of `G`.

This is equivalent to the existence of an isomorphism from `G` to a subgraph of `H`. -/
abbrev IsContained (G : SimpleGraph V) (H : SimpleGraph W) := Nonempty (Copy G H)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

/-- A simple graph contains itself. -/
@[refl] protected theorem IsContained.refl (G : SimpleGraph V) : G ⊑ G := ⟨.id G⟩

protected theorem IsContained.rfl : G ⊑ G := IsContained.refl G

/-- A simple graph contains its subgraphs. -/
theorem IsContained.of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨.ofLE G₁ G₂ h⟩

/-- If `G` is contained in `H` and `H` is contained in `I`, then `G` is contained in `I`. -/
theorem IsContained.trans : G ⊑ H → H ⊑ I → G ⊑ I := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

/-- If `H` is contained in `I` and `G` is contained in `H`, then `G` is contained in `I`. -/
theorem IsContained.trans' : H ⊑ I → G ⊑ H → G ⊑ I := flip IsContained.trans

@[gcongr]
lemma IsContained.mono_right {H' : SimpleGraph W} (h_isub : G ⊑ H) (h_sub : H ≤ H') : G ⊑ H' :=
  h_isub.trans <| IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

@[gcongr]
lemma IsContained.mono_left {G' : SimpleGraph V} (h_sub : G ≤ G') (h_isub : G' ⊑ H) : G ⊑ H :=
  (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

/-- If `G ≃g G'` and `H ≃g H'` then `G` is contained in `H` if and only if `G'` is
contained in `H'`. -/
theorem isContained_congr (e₁ : G ≃g G') (e₂ : H ≃g H') : G ⊑ H ↔ G' ⊑ H' :=
  ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩

lemma isContained_congr_left (e₁ : G ≃g G') : G ⊑ H ↔ G' ⊑ H := isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

lemma isContained_congr_right (e₂ : H ≃g H') : G ⊑ H ↔ G ⊑ H' := isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

instance : IsPreorder (SimpleGraph V) IsContained where
  refl := .refl
  trans _ _ _ := .trans

instance :
    Trans (α := SimpleGraph V) (β := SimpleGraph W) (γ := SimpleGraph X)
      IsContained IsContained IsContained where
  trans := .trans

/-- A simple graph having no vertices is contained in any simple graph. -/
lemma IsContained.of_isEmpty [IsEmpty V] : G ⊑ H :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- `⊥` is contained in any simple graph having sufficiently many vertices. -/
lemma bot_isContained_iff_card_le [Finite V] [Finite W] :
    (⊥ : SimpleGraph V) ⊑ H ↔ Nat.card V ≤ Nat.card W :=
  ⟨fun ⟨f⟩ ↦ Finite.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.bot (Cardinal.lift_mk_le'.mp (by
      simp only [← Nat.cast_card, Cardinal.lift_natCast]; exact_mod_cast h)).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

/-- A simple graph `G` contains the coercion of any of its `G.Subgraph`s. -/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- `H` contains `G` if and only if `H` has a subgraph `H'` and `H'` is isomorphic to `G`. -/
theorem isContained_iff_exists_iso_subgraph :
    G ⊑ H ↔ ∃ H' : H.Subgraph, Nonempty (G ≃g H'.coe) where
  mp := fun ⟨f⟩ ↦ ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨H', ⟨e⟩⟩ ↦ H'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

theorem Copy.degree_le (f : Copy G H) (v : V) [Fintype <| G.neighborSet v]
    [Fintype <| H.neighborSet (f v)] : G.degree v ≤ H.degree (f v) := by
  simpa using Fintype.card_le_of_injective _ (f.mapNeighborSet v).injective

theorem Copy.max_degree_le [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) : G.maxDegree ≤ H.maxDegree := by
  cases isEmpty_or_nonempty V
  · simp
  obtain ⟨v, h⟩ := exists_maximal_degree_vertex G
  grind [degree_le_maxDegree H (f v), f.degree_le v]

theorem IsContained.max_degree_le [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ⊑ H) : G.maxDegree ≤ H.maxDegree := by
  have ⟨f⟩ := h
  exact f.max_degree_le

@[gcongr]
lemma maxDegree_mono {H : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.maxDegree ≤ H.maxDegree :=
  IsContained.of_le hle |>.max_degree_le

theorem Copy.minDegree_le [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : Copy G H} (hf : Function.Surjective f) : G.minDegree ≤ H.minDegree := by
  cases isEmpty_or_nonempty W
  · simp [Function.isEmpty f]
  refine H.le_minDegree_of_forall_le_degree _ fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.degree_le, ← minDegree_le_degree]

theorem Hom.minDegree_le [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : G →g H} (hf : Function.Bijective f) : G.minDegree ≤ H.minDegree :=
  Copy.minDegree_le (f := ⟨f, hf.injective⟩) hf.surjective

end IsContained

section Free

/-- `G.Free H` means that `H` does not contain a copy of `G`. -/
abbrev Free (G : SimpleGraph V) (H : SimpleGraph W) := ¬G ⊑ H

lemma not_free : ¬G.Free H ↔ G ⊑ H := not_not

/-- If `G ≃g G'` and `H ≃g H'` then `H` is `G`-free if and only if `H'` is `G'`-free. -/
theorem free_congr (e₁ : G ≃g G') (e₂ : H ≃g H') : G.Free H ↔ G'.Free H' :=
  (isContained_congr e₁ e₂).not

lemma free_congr_left (e₁ : G ≃g G') : G.Free H ↔ G'.Free H := free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

lemma free_congr_right (e₂ : H ≃g H') : G.Free H ↔ G.Free H' := free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

lemma free_bot (h : G ≠ ⊥) : G.Free (⊥ : SimpleGraph W) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

end Free

/-!
#### Induced containment

`G ⊴ H` (`\trianglelefteq`).
-/

/-- A simple graph `G` is inducingly contained in a simple graph `H` if there exists an induced
subgraph of `H` isomorphic to `G`. This is denoted by `G ⊴ H`. -/
abbrev IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop := Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

protected lemma Copy.isContained (f : Copy G H) : G ⊑ H := ⟨f⟩

protected lemma Embedding.isIndContained (f : G ↪g H) : G ⊴ H := ⟨f⟩

protected lemma Embedding.isContained (f : G ↪g H) : G ⊑ H := f.toCopy.isContained

protected lemma IsIndContained.isContained : G ⊴ H → G ⊑ H := fun ⟨f⟩ ↦ f.isContained

/-- If `G` is isomorphic to `H`, then `G` is contained in `H`. -/
protected lemma Iso.isContained (e : G ≃g H) : G ⊑ H := e.toCopy.isContained

/-- If `G` is isomorphic to `H`, then `H` is contained in `G`. -/
protected lemma Iso.isContained' (e : G ≃g H) : H ⊑ G := e.symm.isContained

/-- If `G` is isomorphic to `H`, then `G` is inducingly contained in `H`. -/
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := e.toEmbedding.isIndContained

/-- If `G` is isomorphic to `H`, then `H` is inducingly contained in `G`. -/
protected lemma Iso.isIndContained' (e : G ≃g H) : H ⊴ G := e.symm.isIndContained

protected lemma Subgraph.IsInduced.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced) :
    G'.coe ⊴ G :=
  ⟨{ toFun := (↑)
     inj' := Subtype.coe_injective
     map_rel_iff' := hG'.adj.symm }⟩

@[refl] lemma IsIndContained.refl (G : SimpleGraph V) : G ⊴ G := ⟨Embedding.refl⟩
lemma IsIndContained.rfl : G ⊴ G := .refl _
@[trans] lemma IsIndContained.trans : G ⊴ H → H ⊴ I → G ⊴ I := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

instance : IsPreorder (SimpleGraph V) IsIndContained where
  refl := .refl
  trans _ _ _ := .trans

instance :
    Trans (α := SimpleGraph V) (β := SimpleGraph W) (γ := SimpleGraph X)
      IsIndContained IsIndContained IsIndContained where
  trans := .trans

lemma IsIndContained.of_isEmpty [IsEmpty V] : G ⊴ H :=
  ⟨{ toFun := isEmptyElim
     inj' := isEmptyElim
     map_rel_iff' := fun {a} ↦ isEmptyElim a }⟩

lemma isIndContained_iff_exists_iso_subgraph :
    G ⊴ H ↔ ∃ (H' : H.Subgraph) (_e : G ≃g H'.coe), H'.IsInduced := by
  constructor
  · rintro ⟨f⟩
    refine ⟨Subgraph.map f.toHom ⊤, f.toCopy.isoToSubgraph, ?_⟩
    simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

theorem isIndContained_iff_exists_iso_induce : G ⊴ H ↔ ∃ s, Nonempty (G ≃g H.induce s) :=
  ⟨fun ⟨f⟩ ↦ ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ ↦ ⟨.comp (.induce s) f⟩⟩

@[simp] lemma top_isIndContained_iff_top_isContained :
    (⊤ : SimpleGraph V) ⊴ H ↔ (⊤ : SimpleGraph V) ⊑ H :=
  ⟨IsIndContained.isContained, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩

@[simp] lemma compl_isIndContained_compl : Gᶜ ⊴ Hᶜ ↔ G ⊴ H :=
  Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl

theorem isContained_iff_exists_le_comap : G ⊑ H ↔ ∃ (f : V ↪ W), G ≤ H.comap f :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, f.toHom.le_comap⟩, fun ⟨f, h⟩ ↦ ⟨⟨f, (h ·)⟩, f.injective⟩⟩

theorem isIndContained_iff_exists_comap_eq : G ⊴ H ↔ ∃ (f : V ↪ W), H.comap f = G :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ ↦ ⟨f, h ▸ .rfl⟩⟩

/-!
### Counting copies

For finite `G` and `H`, we count labeled and unlabeled copies of `G` in `H`.
-/

section CopyCount

/-- `H.copyCount G` is the number of labeled copies of `G` in `H`, i.e. the number of injective
graph homomorphisms from `G` to `H`. See `SimpleGraph.subCount` for the number of unlabeled
copies. -/
noncomputable def copyCount (H : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Nat.card (Copy G H)

lemma copyCount_eq_nat_card (H : SimpleGraph W) (G : SimpleGraph V) :
    H.copyCount G = Nat.card (Copy G H) := by rw [copyCount]

@[deprecated (since := "2026-04-30")] alias labelledCopyCount := copyCount

private instance [IsEmpty V] : Nonempty (Copy G H) := IsContained.of_isEmpty

@[simp] lemma copyCount_of_isEmpty [IsEmpty V] (H : SimpleGraph W) (G : SimpleGraph V) :
    H.copyCount G = 1 := Nat.card_unique

@[deprecated (since := "2026-04-30")]
alias labelledCopyCount_of_isEmpty := copyCount_of_isEmpty

@[simp] lemma copyCount_eq_zero [Finite V] [Finite W] : H.copyCount G = 0 ↔ G.Free H := by
  rw [copyCount, Nat.card_eq_zero, or_iff_left (Finite.not_infinite inferInstance)]
  simp [Free, IsContained]

@[deprecated (since := "2026-04-30")] alias labelledCopyCount_eq_zero := copyCount_eq_zero

@[simp] lemma copyCount_pos [Finite V] [Finite W] : 0 < H.copyCount G ↔ G ⊑ H := by
  simp [Nat.pos_iff_ne_zero, copyCount_eq_zero]

@[deprecated (since := "2026-04-30")] alias labelledCopyCount_pos := copyCount_pos

end CopyCount

section SubCount

/-- `G.Sub H` is the type of `SimpleGraph.Subgraph`s of `H` isomorphic to `G`. The corresponding
count is `SimpleGraph.subCount`. -/
abbrev Sub (G : SimpleGraph V) (H : SimpleGraph W) : Type _ :=
  {H' : H.Subgraph // Nonempty (G ≃g H'.coe)}

/-- `H.subCount G` is the number of `SimpleGraph.Subgraph`s of `H` isomorphic to `G`. See
`SimpleGraph.copyCount` for the number of labeled copies. -/
noncomputable def subCount (H : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Nat.card (G.Sub H)

lemma subCount_eq_nat_card (H : SimpleGraph W) (G : SimpleGraph V) :
    H.subCount G = Nat.card (G.Sub H) := by rw [subCount]

@[simp] lemma subCount_eq_zero [Finite W] : H.subCount G = 0 ↔ G.Free H := by
  rw [subCount, Nat.card_eq_zero, or_iff_left (Finite.not_infinite inferInstance), isEmpty_subtype]
  simp [Free, isContained_iff_exists_iso_subgraph]

@[simp] lemma subCount_pos [Finite W] : 0 < H.subCount G ↔ G ⊑ H := by
  simp [Nat.pos_iff_ne_zero, subCount_eq_zero]

/-- There are at least as many labeled copies of `G` in `H` as there are unlabeled ones. -/
lemma subCount_le_copyCount [Finite V] [Finite W] : H.subCount G ≤ H.copyCount G := by
  rw [subCount, copyCount]
  apply Nat.card_le_card_of_surjective
    (fun c : Copy G H ↦ (⟨c.toSubgraph, ⟨c.isoToSubgraph⟩⟩ : G.Sub H))
  rintro ⟨H', hG'⟩
  obtain ⟨c, hc⟩ : ∃ c, Copy.toSubgraph c = H' := by
    rwa [← Set.mem_range, Copy.range_toSubgraph]
  exact ⟨c, Subtype.ext hc⟩

instance uniqueSubBot [Finite W] (H : SimpleGraph W) : Unique ((⊥ : SimpleGraph W).Sub H) where
  default := ⟨{ verts := .univ, Adj := ⊥, adj_sub := False.elim, edge_vert := False.elim },
              ⟨(Equiv.Set.univ _).symm, by simp⟩⟩
  uniq := fun ⟨H', ⟨e⟩⟩ ↦ Subtype.ext <| Subgraph.ext
    (Set.eq_univ_of_forall fun v ↦ by
      obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp
        (Subtype.val_injective.comp e.toEquiv.injective)) v
      exact hw ▸ (e.toEquiv w).prop)
    (funext₂ fun a b ↦ eq_false fun hadj ↦ absurd (e.symm.map_rel_iff.mpr hadj.coe) (by simp))

@[simp] lemma subCount_bot [Finite W] (H : SimpleGraph W) :
    H.subCount (⊥ : SimpleGraph W) = 1 :=
  Nat.card_unique

private instance [IsEmpty V] : Nonempty (G.Sub H) :=
  let ⟨H', ⟨e⟩⟩ := (IsContained.of_isEmpty (G := G) (H := H)).exists_iso_subgraph
  ⟨⟨H', ⟨e⟩⟩⟩

private instance [IsEmpty V] : Subsingleton (G.Sub H) :=
  ⟨fun ⟨H', ⟨e⟩⟩ ⟨H'', ⟨e'⟩⟩ ↦ Subtype.ext <|
    (H'.eq_bot_iff_verts_eq_empty.mpr (Set.isEmpty_coe_sort.mp e.toEquiv.symm.isEmpty)).trans
    (H''.eq_bot_iff_verts_eq_empty.mpr (Set.isEmpty_coe_sort.mp e'.toEquiv.symm.isEmpty)).symm⟩

@[simp] lemma subCount_of_isEmpty [IsEmpty V] (H : SimpleGraph W) (G : SimpleGraph V) :
    H.subCount G = 1 := Nat.card_unique

end SubCount

/-!
### Killing all copies of a graph

We can remove not too many edges from a graph `H` to get a graph `H'` that doesn't contain `G`.
By construction, `H.killCopies G` doesn't contain `G` and differs from `H` by at most one edge
per copy.
-/

set_option backward.privateInPublic true in
private lemma aux (hG : G ≠ ⊥) {H' : H.Subgraph} :
    Nonempty (G ≃g H'.coe) → H'.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hG
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ ↦ Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `H.killCopies G` is a subgraph of `H` where an *arbitrary* edge was removed from each copy of
`G` in `H`. By construction, it doesn't contain `G` (unless `G` had no edges) and has at most the
number of copies of `G` edges less than `H`. See `free_killCopies` and
`le_card_edgeFinset_killCopies` for these two properties. -/
noncomputable irreducible_def killCopies (H : SimpleGraph W) (G : SimpleGraph V) :
    SimpleGraph W := by
  classical exact
  if hG : G = ⊥ then H
  else H.deleteEdges <| ⋃ (H' : H.Subgraph) (hG' : Nonempty (G ≃g H'.coe)), {(aux hG hG').some}

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a subgraph of `H`. -/
lemma killCopies_le_left : H.killCopies G ≤ H := by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]

@[simp] lemma killCopies_bot (H : SimpleGraph W) : H.killCopies (⊥ : SimpleGraph V) = H := by
  rw [killCopies]; exact dif_pos rfl

private lemma killCopies_of_ne_bot (hG : G ≠ ⊥) (H : SimpleGraph W) :
    H.killCopies G =
      H.deleteEdges (⋃ (H' : H.Subgraph) (hG' : Nonempty (G ≃g H'.coe)), {(aux hG hG').some}) := by
  rw [killCopies]; exact dif_neg hG

/-- `H.killCopies G` has no effect on `H` if and only if `H` already contained no copies of `G`. See
`Free.killCopies_eq_left` for the reverse implication with no assumption on `G`. -/
lemma killCopies_eq_left (hG : G ≠ ⊥) : H.killCopies G = H ↔ G.Free H := by
  simp only [killCopies_of_ne_bot hG, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_comm _ H.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun H' ↦ ⟨fun h ↦ ⟨fun f ↦ h _
    (Subgraph.edgeSet_subset _ <| (aux hG ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ ↦ h.elim⟩

protected lemma Free.killCopies_eq_left (hGH : G.Free H) : H.killCopies G = H := by
  obtain rfl | hG := eq_or_ne G ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hG).2 hGH

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a graph that doesn't
contain `G`. -/
lemma free_killCopies (hG : G ≠ ⊥) : G.Free (H.killCopies G) := by
  rw [killCopies_of_ne_bot hG, deleteEdges, Free, isContained_iff_exists_iso_subgraph]
  rintro ⟨H', hGH'⟩
  have hH' : (H'.map <| .ofLE (sdiff_le : H \ _ ≤ H)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hG hGH').image _
  set e := hH'.some with he
  have : e ∈ _ := hH'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 H'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' ∈ H'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (H'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hGH'.some⟩ ?_
  rw [Sym2.map_map, Set.mem_singleton_iff, ← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

variable [Fintype H.edgeSet]

noncomputable instance killCopies.edgeSet.instFintype : Fintype (H.killCopies G).edgeSet :=
  .ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) <| Set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edgeFinset_killCopies [Finite W] :
    #H.edgeFinset - H.subCount G ≤ #(H.killCopies G).edgeFinset := by
  classical
  obtain rfl | hG := eq_or_ne G ⊥
  · simp [← card_edgeSet]
  cases nonempty_fintype (G.Sub H)
  let f (H' : G.Sub H) := (aux hG H'.2).some
  calc #H.edgeFinset - H.subCount G
      = #H.edgeFinset - Fintype.card (G.Sub H) := by rw [subCount, Nat.card_eq_fintype_card]
    _ ≤ #H.edgeFinset - #(Finset.univ.image f) := Nat.sub_le_sub_left Finset.card_image_le _
    _ ≤ #(H.edgeFinset \ Finset.univ.image f) := le_card_sdiff ..
    _ = #(H.killCopies G).edgeFinset := by
        congr 1
        ext e
        induction e using Sym2.inductionOn with | hf v w
        simp [mem_edgeSet, killCopies_of_ne_bot hG, f, eq_comm]

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edgeFinset_killCopies_add_subCount [Finite W] :
    #H.edgeFinset ≤ #(H.killCopies G).edgeFinset + H.subCount G :=
  tsub_le_iff_right.1 le_card_edgeFinset_killCopies

end SimpleGraph
