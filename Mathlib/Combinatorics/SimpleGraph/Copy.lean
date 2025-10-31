/-
Copyright (c) 2023 Yaël Dillies, Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Mitchell Horner
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Containment of graphs

This file introduces the concept of one simple graph containing a copy of another.

For two simple graphs `G` and `H`, a *copy* of `G` in `H` is a (not necessarily induced) subgraph of
`H` isomorphic to `G`.

If there exists a copy of `G` in `H`, we say that `H` *contains* `G`. This is equivalent to saying
that there is an injective graph homomorphism `G → H` between them (this is **not** the same as a
graph embedding, as we do not require the subgraph to be induced).

If there exists an induced copy of `G` in `H`, we say that `H` *inducingly contains* `G`. This is
equivalent to saying that there is a graph embedding `G ↪ H`.

## Main declarations

Containment:
* `SimpleGraph.Copy G H` is the type of copies of `G` in `H`, implemented as the subtype of
  *injective* homomorphisms.
* `SimpleGraph.IsContained G H`, `G ⊑ H` is the relation that `H` contains a copy of `G`, that
  is, the type of copies of `G` in `H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to a subgraph of `H`.
  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `H` is `G`-free, that is, `H` does not contain a copy of
  `G`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.
* `SimpleGraph.killCopies G H`: Subgraph of `G` that does not contain `H`. Obtained by arbitrarily
  removing an edge from each copy of `H` in `G`.
* `SimpleGraph.copyCount G H`: Number of copies of `H` in `G`, i.e. number of subgraphs of `G`
  isomorphic to `H`.
* `SimpleGraph.labelledCopyCount G H`: Number of labelled copies of `H` in `G`, i.e. number of
  graph embeddings from `H` to `G`.

Induced containment:
* Induced copies of `G` inside `H` are already defined as `G ↪g H`.
* `SimpleGraph.IsIndContained G H` : `G` is contained as an induced subgraph in `H`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.IsContained G H`.
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Count induced copies of a graph inside another.
* Make `copyCount`/`labelledCopyCount` computable (not necessarily efficiently).
-/

open Finset Function
open Fintype (card)

namespace SimpleGraph
variable {V W X α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

/-!
### Copies

#### Not necessarily induced copies

A copy of a subgraph `G` inside a subgraph `H` is an embedding of the vertices of `G` into the
vertices of `H`, such that adjacency in `G` implies adjacency in `H`.

We capture this concept by injective graph homomorphisms.
-/

section Copy

/-- The type of copies as a subtype of *injective* homomorphisms. -/
structure Copy (A : SimpleGraph α) (B : SimpleGraph β) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : A →g B
  injective' : Injective toHom

/-- An injective homomorphism gives rise to a copy. -/
abbrev Hom.toCopy (f : A →g B) (h : Injective f) : Copy A B := .mk f h

/-- An embedding gives rise to a copy. -/
abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

/-- An isomorphism gives rise to a copy. -/
abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

instance : FunLike (Copy A B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

lemma injective (f : Copy A B) : Injective f.toHom := f.injective'

@[ext] lemma ext {f g : Copy A B} : (∀ a, f a = g a) → f = g := DFunLike.ext _ _

@[simp] lemma coe_toHom (f : Copy A B) : ⇑f.toHom = f := rfl
@[simp] lemma toHom_apply (f : Copy A B) (a : α) : ⇑f.toHom a = f a := rfl

@[simp] lemma coe_mk (f : A →g B) (hf) : ⇑(.mk f hf : Copy A B) = f := rfl

/-- A copy induces an embedding of edge sets. -/
def mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where
  toFun := f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A copy induces an embedding of neighbor sets. -/
def mapNeighborSet (f : Copy A B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- A copy gives rise to an embedding of vertex types. -/
def toEmbedding (f : Copy A B) : α ↪ β := ⟨f, f.injective⟩

/-- The identity copy from a simple graph to itself. -/
@[refl] def id (G : SimpleGraph V) : Copy G G := ⟨Hom.id, Function.injective_id⟩

@[simp, norm_cast] lemma coe_id : ⇑(id G) = _root_.id := rfl

/-- The composition of copies is a copy. -/
def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]
theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/-- The copy from a subgraph to the supergraph. -/
def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) : Copy G₁ G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
theorem coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f := by ext; simp

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl

@[simp] theorem ofLE_refl : ofLE G G le_rfl = id G := by ext; simp

@[simp]
theorem ofLE_comp (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ≤ G₃) :
    (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/-- The copy from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G := (Embedding.induce s).toCopy

/-- The copy of `⊥` in any simple graph that can embed its vertices. -/
protected def bot (f : α ↪ β) : Copy (⊥ : SimpleGraph α) B := ⟨⟨f, False.elim⟩, f.injective⟩

/-- The isomorphism from a subgraph of `A` to its map under a copy `f : Copy A B`. -/
noncomputable def isoSubgraphMap (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- The subgraph of `B` corresponding to a copy of `A` inside `B`. -/
abbrev toSubgraph (f : Copy A B) : B.Subgraph := .map f.toHom ⊤

/-- The isomorphism from `A` to its copy under `f : Copy A B`. -/
noncomputable def isoToSubgraph (f : Copy A B) : A ≃g f.toSubgraph.coe :=
  (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm

@[simp] lemma range_toSubgraph :
    .range (toSubgraph (A := A)) = {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} := by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]

lemma toSubgraph_surjOn :
    Set.SurjOn (toSubgraph (A := A)) .univ {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} :=
  fun H' hH' ↦ by simpa

instance [Subsingleton (V → W)] : Subsingleton (G.Copy H) := DFunLike.coe_injective.subsingleton

instance [Fintype {f : G →g H // Injective f}] : Fintype (G.Copy H) :=
  .ofEquiv {f : G →g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

/-- A copy of `⊤` gives rise to an embedding of `⊤`. -/
@[simps!]
def topEmbedding (f : Copy (⊤ : SimpleGraph α) G) : (⊤ : SimpleGraph α) ↪g G :=
  { f.toEmbedding with
    map_rel_iff' := fun {v w} ↦ ⟨fun h ↦ by simpa using h.ne, f.toHom.map_adj⟩}

end Copy

/-- A `Subgraph G` gives rise to a copy from the coercion to `G`. -/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G := G'.hom.toCopy hom_injective

end Copy

/-!
#### Induced copies

An induced copy of a graph `G` inside a graph `H` is an embedding from the vertices of
`G` into the vertices of `H` which preserves the adjacency relation.

This is already captured by the notion of graph embeddings, defined as `G ↪g H`.

### Containment

#### Not necessarily induced containment

A graph `H` *contains* a graph `G` if there is some copy `f : Copy G H` of `G` inside `H`. This
amounts to `H` having a subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊑ H` (`\squb`).
-/

section IsContained

/-- The relation `IsContained A B`, `A ⊑ B` says that `B` contains a copy of `A`.

This is equivalent to the existence of an isomorphism from `A` to a subgraph of `B`. -/
abbrev IsContained (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

/-- A simple graph contains itself. -/
@[refl] protected theorem IsContained.refl (G : SimpleGraph V) : G ⊑ G := ⟨.id G⟩

protected theorem IsContained.rfl : G ⊑ G := IsContained.refl G

/-- A simple graph contains its subgraphs. -/
theorem IsContained.of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨.ofLE G₁ G₂ h⟩

/-- If `A` contains `B` and `B` contains `C`, then `A` contains `C`. -/
theorem IsContained.trans : A ⊑ B → B ⊑ C → A ⊑ C := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

/-- If `B` contains `C` and `A` contains `B`, then `A` contains `C`. -/
theorem IsContained.trans' : B ⊑ C → A ⊑ B → A ⊑ C := flip IsContained.trans

lemma IsContained.mono_right {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B ≤ B') : A ⊑ B' :=
  h_isub.trans <| IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

lemma IsContained.mono_left {A' : SimpleGraph α} (h_sub : A ≤ A') (h_isub : A' ⊑ B) : A ⊑ B :=
  (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

/-- If `A ≃g H` and `B ≃g G` then `A` is contained in `B` if and only if `H` is contained
in `G`. -/
theorem isContained_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A ⊑ B ↔ H ⊑ G :=
  ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩

lemma isContained_congr_left (e₁ : A ≃g B) : A ⊑ C ↔ B ⊑ C := isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

lemma isContained_congr_right (e₂ : B ≃g C) : A ⊑ B ↔ A ⊑ C := isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

/-- A simple graph having no vertices is contained in any simple graph. -/
lemma IsContained.of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- `⊥` is contained in any simple graph having sufficiently many vertices. -/
lemma bot_isContained_iff_card_le [Fintype α] [Fintype β] :
    (⊥ : SimpleGraph α) ⊑ B ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨f⟩ ↦ Fintype.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
theorem isContained_iff_exists_iso_subgraph :
    A ⊑ B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) where
  mp := fun ⟨f⟩ ↦ ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨B', ⟨e⟩⟩ ↦ B'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

end IsContained

section Free

/-- `A.Free B` means that `B` does not contain a copy of `A`. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

lemma not_free : ¬A.Free B ↔ A ⊑ B := not_not

/-- If `A ≃g H` and `B ≃g G` then `B` is `A`-free if and only if `G` is `H`-free. -/
theorem free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free B ↔ H.Free G :=
  (isContained_congr e₁ e₂).not

lemma free_congr_left (e₁ : A ≃g B) : A.Free C ↔ B.Free C := free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

lemma free_congr_right (e₂ : B ≃g C) : A.Free B ↔ A.Free C := free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

lemma free_bot (h : A ≠ ⊥) : A.Free (⊥ : SimpleGraph β) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

end Free

/-!
#### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is inducingly contained in `H`" by `G ⊴ H` (`\trianglelefteq`).
-/

/-- A simple graph `G` is inducingly contained in a simple graph `H` if there exists an induced
subgraph of `H` isomorphic to `G`. This is denoted by `G ⊴ H`. -/
def IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop := Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

protected lemma IsIndContained.isContained : G ⊴ H → G ⊑ H := fun ⟨f⟩ ↦ ⟨f.toCopy⟩

/-- If `G` is isomorphic to `H`, then `G` is inducingly contained in `H`. -/
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := ⟨e⟩

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

@[simp] lemma top_isIndContained_iff_top_isContained :
    (⊤ : SimpleGraph V) ⊴ H ↔ (⊤ : SimpleGraph V) ⊑ H :=
  ⟨IsIndContained.isContained, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩

@[simp] lemma compl_isIndContained_compl : Gᶜ ⊴ Hᶜ ↔ G ⊴ H :=
  Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.

#### Not necessarily induced copies
-/

section LabelledCopyCount
variable [Fintype V] [Fintype W]

/-- `G.labelledCopyCount H` is the number of labelled copies of `H` in `G`, i.e. the number of graph
embeddings from `H` to `G`. See `SimpleGraph.copyCount` for the number of unlabelled copies. -/
noncomputable def labelledCopyCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ := by
  classical exact Fintype.card (Copy H G)

@[simp] lemma labelledCopyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.labelledCopyCount H = 1 := by
  convert Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }

@[simp] lemma labelledCopyCount_eq_zero : G.labelledCopyCount H = 0 ↔ H.Free G := by
  simp [labelledCopyCount, Fintype.card_eq_zero_iff]

@[simp] lemma labelledCopyCount_pos : 0 < G.labelledCopyCount H ↔ H ⊑ G := by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]

end LabelledCopyCount

section CopyCount
variable [Fintype V]

/-- `G.copyCount H` is the number of unlabelled copies of `H` in `G`, i.e. the number of subgraphs
of `G` isomorphic to `H`. See `SimpleGraph.labelledCopyCount` for the number of labelled copies. -/
noncomputable def copyCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ := by
  classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}

lemma copyCount_eq_card_image_copyToSubgraph [Fintype {f : H →g G // Injective f}]
    [DecidableEq G.Subgraph] :
    copyCount G H = #((Finset.univ : Finset (H.Copy G)).image Copy.toSubgraph) := by
  rw [copyCount]
  congr
  refine Finset.coe_injective ?_
  simpa [-Copy.range_toSubgraph] using Copy.range_toSubgraph.symm

@[simp] lemma copyCount_eq_zero : G.copyCount H = 0 ↔ H.Free G := by
  simp [copyCount, Free, -nonempty_subtype, isContained_iff_exists_iso_subgraph,
    filter_eq_empty_iff]

@[simp] lemma copyCount_pos : 0 < G.copyCount H ↔ H ⊑ G := by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]

/-- There's at least as many labelled copies of `H` in `G` than unlabelled ones. -/
lemma copyCount_le_labelledCopyCount [Fintype W] : G.copyCount H ≤ G.labelledCopyCount H := by
  classical rw [copyCount_eq_card_image_copyToSubgraph]; exact card_image_le

@[simp] lemma copyCount_bot (G : SimpleGraph V) : copyCount G (⊥ : SimpleGraph V) = 1 := by
  classical
  rw [copyCount]
  convert card_singleton (α := G.Subgraph)
    { verts := .univ
      Adj := ⊥
      adj_sub := False.elim
      edge_vert := False.elim }
  simp only [eq_singleton_iff_unique_mem, mem_filter_univ, Nonempty.forall]
  refine ⟨⟨⟨(Equiv.Set.univ _).symm, by simp⟩⟩, fun H' e ↦
    Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab ↦ e.symm.map_rel_iff.2 hab.coe

@[simp] lemma copyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.copyCount H = 1 := by
  cases nonempty_fintype W
  exact (copyCount_le_labelledCopyCount.trans_eq <| labelledCopyCount_of_isEmpty ..).antisymm <|
    copyCount_pos.2 <| .of_isEmpty

end CopyCount

/-!
#### Induced copies

TODO

### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

#### Killing not necessarily induced copies

`SimpleGraph.killCopies G H` is a subgraph of `G` where an edge was removed from each copy of `H` in
`G`. By construction, it doesn't contain `H` and has at most the number of copies of `H` edges less
than `G`.
-/

private lemma aux (hH : H ≠ ⊥) {G' : G.Subgraph} :
    Nonempty (H ≃g G'.coe) → G'.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hH
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ ↦ Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

/-- `G.killCopies H` is a subgraph of `G` where an *arbitrary* edge was removed from each copy of
`H` in `G`. By construction, it doesn't contain `H` (unless `H` had no edges) and has at most the
number of copies of `H` edges less than `G`. See `free_killCopies` and
`le_card_edgeFinset_killCopies` for these two properties. -/
noncomputable irreducible_def killCopies (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph V := by
  classical exact
  if hH : H = ⊥ then G
  else G.deleteEdges <| ⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}

/-- Removing an edge from `G` for each subgraph isomorphic to `H` results in a subgraph of `G`. -/
lemma killCopies_le_left : G.killCopies H ≤ G := by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]

@[simp] lemma killCopies_bot (G : SimpleGraph V) : G.killCopies (⊥ : SimpleGraph W) = G := by
  rw [killCopies]; exact dif_pos rfl

private lemma killCopies_of_ne_bot (hH : H ≠ ⊥) (G : SimpleGraph V) :
    G.killCopies H =
      G.deleteEdges (⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}) := by
  rw [killCopies]; exact dif_neg hH

/-- `G.killCopies H` has no effect on `G` if and only if `G` already contained no copies of `H`. See
`Free.killCopies_eq_left` for the reverse implication with no assumption on `H`. -/
lemma killCopies_eq_left (hH : H ≠ ⊥) : G.killCopies H = G ↔ H.Free G := by
  simp only [killCopies_of_ne_bot hH, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_swap _ G.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun G' ↦ ⟨fun h ↦ ⟨fun f ↦ h _
    (Subgraph.edgeSet_subset _ <| (aux hH ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ ↦ h.elim⟩

protected lemma Free.killCopies_eq_left (hHG : H.Free G) : G.killCopies H = G := by
  obtain rfl | hH := eq_or_ne H ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hH).2 hHG

/-- Removing an edge from `G` for each subgraph isomorphic to `H` results in a graph that doesn't
contain `H`. -/
lemma free_killCopies (hH : H ≠ ⊥) : H.Free (G.killCopies H) := by
  rw [killCopies_of_ne_bot hH, deleteEdges, Free, isContained_iff_exists_iso_subgraph]
  rintro ⟨G', hHG'⟩
  have hG' : (G'.map <| .ofLE (sdiff_le : G \ _ ≤ G)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hH hHG').image _
  set e := hG'.some with he
  have : e ∈ _ := hG'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 G'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' ∈ G'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (G'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hHG'.some⟩ ?_
  rw [Sym2.map_map, Set.mem_singleton_iff, ← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

variable [Fintype G.edgeSet]

noncomputable instance killCopies.edgeSet.instFintype : Fintype (G.killCopies H).edgeSet :=
  .ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) <| Set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edgeFinset_killCopies [Fintype V] :
    #G.edgeFinset - G.copyCount H ≤ #(G.killCopies H).edgeFinset := by
  classical
  obtain rfl | hH := eq_or_ne H ⊥
  · simp
  let f (G' : {G' : G.Subgraph // Nonempty (H ≃g G'.coe)}) := (aux hH G'.2).some
  calc
    _ = #G.edgeFinset - card {G' : G.Subgraph // Nonempty (H ≃g G'.coe)} := ?_
    _ ≤ #G.edgeFinset - #(univ.image f) := Nat.sub_le_sub_left card_image_le _
    _ = #G.edgeFinset - #(Set.range f).toFinset := by rw [Set.toFinset_range]
    _ ≤ #(G.edgeFinset \ (Set.range f).toFinset) := le_card_sdiff ..
    _ = #(G.killCopies H).edgeFinset := ?_
  · simp only [Set.toFinset_card]
    rw [← Set.toFinset_card, ← edgeFinset, copyCount, ← card_subtype, subtype_univ, card_univ]
  simp only [killCopies_of_ne_bot, hH, Ne, not_false_iff,
    Set.toFinset_card, edgeSet_deleteEdges]
  simp only [Finset.sdiff_eq_inter_compl, Set.diff_eq, ← Set.iUnion_singleton_eq_range,
    Set.coe_toFinset, coe_filter, Set.iUnion_subtype, ← Fintype.card_coe,
    ← Finset.coe_sort_coe, coe_inter, coe_compl, Set.coe_toFinset, Set.compl_iUnion,
    Fintype.card_ofFinset, f]

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edgeFinset_killCopies_add_copyCount [Fintype V] :
    #G.edgeFinset ≤ #(G.killCopies H).edgeFinset + G.copyCount H :=
  tsub_le_iff_right.1 le_card_edgeFinset_killCopies

/-!
#### Killing induced copies

TODO
-/

end SimpleGraph
