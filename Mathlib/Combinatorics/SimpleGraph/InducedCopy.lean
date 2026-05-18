/-
Copyright (c) 2023 Yaël Dillies, Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Mitchell Horner, Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Induced containment of graphs

This file develops the induced analogues of the containment notions from
`Mathlib/Combinatorics/SimpleGraph/Copy.lean`.

For two simple graphs `G` and `H`, an *induced copy* of `G` in `H` is an induced subgraph of `H`
isomorphic to `G`. Equivalently, it is a graph embedding `Embedding G H`.

## Main declarations

* `SimpleGraph.IsIndContained G H`, `G ⊴ H` is the relation that `H` contains an induced copy of
  `G`, that is, the type `Embedding G H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to an induced subgraph of `H`.
* `SimpleGraph.IndFree` is the predicate that `H` does not contain an induced copy of `G`. This
  is the negation of `SimpleGraph.IsIndContained` implemented for convenience.
* `SimpleGraph.UnlabeledEmbedding G H`: Type of induced `SimpleGraph.Subgraph`s of `H`
  isomorphic to `G`.
* `SimpleGraph.embeddingCount H G`: Number of induced labeled copies of `G` in `H`, i.e. the
  number of graph embeddings `Embedding G H`.
* `SimpleGraph.unlabeledEmbeddingCount H G`: Number of induced `SimpleGraph.Subgraph`s of `H`
  isomorphic to `G`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## Naming convention

As in `Mathlib/Combinatorics/SimpleGraph/Copy.lean`, the letter `G` denotes the guest graph and
`H` the host. Types are guest-first (`UnlabeledEmbedding G H`, `IsIndContained G H`); operations are
host-first (`H.embeddingCount G`, `H.unlabeledEmbeddingCount G`).

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Kill induced copies of a graph inside another.
-/

public section

open Finset Function

namespace SimpleGraph
variable {V V' W W' X : Type*}
  {G G₁ G₂ : SimpleGraph V} {G' : SimpleGraph V'}
  {H : SimpleGraph W} {H' : SimpleGraph W'}
  {I : SimpleGraph X}

/-!
### Embedding to subgraph

For a graph embedding `f : Embedding G H`, the image is an induced subgraph of `H` isomorphic
to `G`. This packages the image as a `H.Subgraph`, together with the inducedness and isomorphism
characterisations needed downstream.
-/

namespace Embedding

/-- The induced subgraph corresponding to an embedding. -/
abbrev toSubgraph (f : Embedding G H) : H.Subgraph := f.toCopy.toSubgraph

@[simp] lemma toSubgraph_isInduced (f : Embedding G H) : (toSubgraph f).IsInduced := by
  simp [toSubgraph, Copy.toSubgraph, Subgraph.IsInduced, Relation.map_apply_apply, f.injective]

@[simp] lemma range_toSubgraph :
    Set.range (toSubgraph : (Embedding G H) → H.Subgraph) =
      {H' : H.Subgraph | H'.IsInduced ∧ Nonempty (G ≃g H'.coe)} := by
  ext H'
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨toSubgraph_isInduced f, ⟨f.toCopy.isoToSubgraph⟩⟩
  · rintro ⟨hInd, ⟨e⟩⟩
    refine ⟨(ofIsInduced H' hInd).comp e.toEmbedding, ?_⟩
    have h : ((ofIsInduced H' hInd).comp e.toEmbedding).toHom =
        H'.hom.comp e.toHom := by ext; simp
    simp [toSubgraph, Copy.toSubgraph, h, Subgraph.map_comp]

end Embedding

/-!
### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `Embedding G H`. This
amounts to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is inducingly contained in `H`" by `G ⊴ H` (`\trianglelefteq`).
-/

section IsIndContained

/-- The relation `IsIndContained G H`, `G ⊴ H` says that `H` contains an induced copy of `G`,
i.e. there exists a graph embedding `Embedding G H`.

This is equivalent to the existence of an isomorphism from `G` to an induced subgraph of `H`. -/
abbrev IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop := Nonempty (Embedding G H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

protected lemma Embedding.isIndContained (f : Embedding G H) : G ⊴ H := ⟨f⟩

protected lemma IsIndContained.isContained : G ⊴ H → G ⊑ H := fun ⟨f⟩ ↦ f.isContained

/-- If `G` is isomorphic to `H`, then `G` is inducingly contained in `H`. -/
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := e.toEmbedding.isIndContained

/-- If `G` is isomorphic to `H`, then `H` is inducingly contained in `G`. -/
protected lemma Iso.isIndContained' (e : G ≃g H) : H ⊴ G := e.symm.isIndContained

protected lemma Subgraph.IsInduced.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced) :
    G'.coe ⊴ G :=
  ⟨Embedding.ofIsInduced G' hG'⟩

/-- A simple graph inducingly contains itself. -/
@[refl] protected theorem IsIndContained.refl (G : SimpleGraph V) : G ⊴ G := ⟨Embedding.refl⟩

protected theorem IsIndContained.rfl : G ⊴ G := IsIndContained.refl G

/-- If `G` is inducingly contained in `H` and `H` is inducingly contained in `I`, then `G` is
inducingly contained in `I`. -/
protected theorem IsIndContained.trans : G ⊴ H → H ⊴ I → G ⊴ I :=
  fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

/-- If `H` is inducingly contained in `I` and `G` is inducingly contained in `H`, then `G` is
inducingly contained in `I`. -/
protected theorem IsIndContained.trans' : H ⊴ I → G ⊴ H → G ⊴ I := flip IsIndContained.trans

/-- If `G ≃g G'` and `H ≃g H'` then `G` is inducingly contained in `H` if and only if `G'` is
inducingly contained in `H'`. -/
theorem isIndContained_congr (e₁ : G ≃g G') (e₂ : H ≃g H') : G ⊴ H ↔ G' ⊴ H' :=
  ⟨.trans' ⟨e₂.toEmbedding⟩ ∘ .trans ⟨e₁.symm.toEmbedding⟩,
   .trans' ⟨e₂.symm.toEmbedding⟩ ∘ .trans ⟨e₁.toEmbedding⟩⟩

lemma isIndContained_congr_left (e₁ : G ≃g G') : G ⊴ H ↔ G' ⊴ H := isIndContained_congr e₁ .refl

alias ⟨_, IsIndContained.congr_left⟩ := isIndContained_congr_left

lemma isIndContained_congr_right (e₂ : H ≃g H') : G ⊴ H ↔ G ⊴ H' := isIndContained_congr .refl e₂

alias ⟨_, IsIndContained.congr_right⟩ := isIndContained_congr_right

instance : IsPreorder (SimpleGraph V) IsIndContained where
  refl := .refl
  trans _ _ _ := .trans

instance :
    Trans (α := SimpleGraph V) (β := SimpleGraph W) (γ := SimpleGraph X)
      IsIndContained IsIndContained IsIndContained where
  trans := .trans

lemma IsIndContained.of_isEmpty [IsEmpty V] : G ⊴ H :=
  ⟨⟨⟨isEmptyElim, isEmptyElim⟩, fun {a} ↦ isEmptyElim a⟩⟩

theorem isIndContained_iff_exists_iso_subgraph :
    G ⊴ H ↔ ∃ H' : H.Subgraph, H'.IsInduced ∧ Nonempty (G ≃g H'.coe) where
  mp := fun ⟨f⟩ ↦ ⟨f.toCopy.toSubgraph,
    by simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective],
    ⟨f.toCopy.isoToSubgraph⟩⟩
  mpr := fun ⟨H', hH', ⟨e⟩⟩ ↦ e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

theorem isIndContained_iff_exists_iso_induce : G ⊴ H ↔ ∃ s, Nonempty (G ≃g H.induce s) :=
  ⟨fun ⟨f⟩ ↦ ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ ↦ ⟨.comp (.induce s) f⟩⟩

@[simp] lemma top_isIndContained_iff_top_isContained :
    (⊤ : SimpleGraph V) ⊴ H ↔ (⊤ : SimpleGraph V) ⊑ H :=
  ⟨IsIndContained.isContained, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩

theorem top_isIndContained_top_iff : completeGraph V ⊴ completeGraph W ↔ Nonempty (V ↪ W) :=
  ⟨(⟨·.some.toEmbedding⟩), (⟨.completeGraph ·.some⟩)⟩

theorem eq_top_of_isIndContained_top (h : G ⊴ completeGraph W) : G = ⊤ :=
  h.some.comap_eq ▸ comap_top h.some.injective

@[simp] lemma compl_isIndContained_compl : Gᶜ ⊴ Hᶜ ↔ G ⊴ H :=
  Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl

theorem isIndContained_iff_exists_comap_eq : G ⊴ H ↔ ∃ f : V ↪ W, H.comap f = G :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ ↦ ⟨f, h ▸ .rfl⟩⟩

end IsIndContained

section IndFree

/-- `G.IndFree H` means that `H` does not contain an induced copy of `G`. -/
abbrev IndFree (G : SimpleGraph V) (H : SimpleGraph W) := ¬G ⊴ H

lemma not_indFree : ¬G.IndFree H ↔ G ⊴ H := not_not

/-- If `G ≃g G'` and `H ≃g H'` then `H` is induced-`G`-free if and only if `H'` is
induced-`G'`-free. -/
theorem indFree_congr (e₁ : G ≃g G') (e₂ : H ≃g H') : G.IndFree H ↔ G'.IndFree H' :=
  (isIndContained_congr e₁ e₂).not

lemma indFree_congr_left (e₁ : G ≃g G') : G.IndFree H ↔ G'.IndFree H := indFree_congr e₁ .refl

alias ⟨_, IndFree.congr_left⟩ := indFree_congr_left

lemma indFree_congr_right (e₂ : H ≃g H') : G.IndFree H ↔ G.IndFree H' := indFree_congr .refl e₂

alias ⟨_, IndFree.congr_right⟩ := indFree_congr_right

lemma indFree_bot (h : G ≠ ⊥) : G.IndFree (⊥ : SimpleGraph W) :=
  fun hG ↦ free_bot h hG.isContained

end IndFree

/-!
### Counting the induced copies

If `G` and `H` are finite graphs, we can count the number of induced unlabeled and labeled
copies of `G` in `H`.

#### Induced labeled copies
-/

section EmbeddingCount

/-- `H.embeddingCount G` is the number of induced labeled copies of `G` in `H`, i.e. the number
of graph embeddings `Embedding G H`. See `SimpleGraph.unlabeledEmbeddingCount` for the number of
induced unlabeled copies. -/
noncomputable def embeddingCount (H : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Nat.card (Embedding G H)

lemma embeddingCount_eq_nat_card (H : SimpleGraph W) (G : SimpleGraph V) :
    H.embeddingCount G = Nat.card (Embedding G H) := by rw [embeddingCount]

private instance [IsEmpty V] : Unique (Embedding G H) :=
  ⟨⟨RelEmbedding.ofIsEmpty G.Adj H.Adj⟩,
   fun _ => RelEmbedding.ext fun a => isEmptyElim a⟩

@[simp] lemma embeddingCount_of_isEmpty [IsEmpty V] (H : SimpleGraph W) (G : SimpleGraph V) :
    H.embeddingCount G = 1 := Nat.card_unique

instance [Finite V] [Finite W] : Finite (Embedding G H) :=
  Finite.of_injective _ DFunLike.coe_injective

@[simp] lemma embeddingCount_eq_zero [Finite V] [Finite W] :
    H.embeddingCount G = 0 ↔ G.IndFree H := by
  rw [embeddingCount, Nat.card_eq_zero, or_iff_left (Finite.not_infinite inferInstance)]
  simp [IndFree, IsIndContained]

@[simp] lemma embeddingCount_pos [Finite V] [Finite W] : 0 < H.embeddingCount G ↔ G ⊴ H := by
  simp [Nat.pos_iff_ne_zero, embeddingCount_eq_zero]

/-- Every induced labeled copy is a labeled copy. -/
lemma embeddingCount_le_copyCount [Finite V] [Finite W] : H.embeddingCount G ≤ H.copyCount G := by
  rw [embeddingCount, copyCount_eq_nat_card]
  exact Nat.card_le_card_of_injective Embedding.toCopy
    fun _ _ h => RelEmbedding.ext fun w => DFunLike.congr_fun h w

end EmbeddingCount

/-!
#### Induced unlabeled copies
-/

section UnlabeledEmbeddingCount

/-- `G.UnlabeledEmbedding H` is the type of induced `SimpleGraph.Subgraph`s of `H` isomorphic
to `G`. The
corresponding count is `SimpleGraph.unlabeledEmbeddingCount`. -/
abbrev UnlabeledEmbedding (G : SimpleGraph V) (H : SimpleGraph W) : Type _ :=
  {H' : H.Subgraph // H'.IsInduced ∧ Nonempty (G ≃g H'.coe)}

instance [Finite W] : Finite (G.UnlabeledEmbedding H) := Subtype.finite

/-- `H.unlabeledEmbeddingCount G` is the number of induced `SimpleGraph.Subgraph`s of `H`
isomorphic to `G`.
See `SimpleGraph.embeddingCount` for the number of induced labeled copies. -/
noncomputable def unlabeledEmbeddingCount (H : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Nat.card (G.UnlabeledEmbedding H)

lemma unlabeledEmbeddingCount_eq_nat_card (H : SimpleGraph W) (G : SimpleGraph V) :
    H.unlabeledEmbeddingCount G = Nat.card (G.UnlabeledEmbedding H) := by
  rw [unlabeledEmbeddingCount]

@[simp] lemma unlabeledEmbeddingCount_eq_zero [Finite W] :
    H.unlabeledEmbeddingCount G = 0 ↔ G.IndFree H := by
  rw [unlabeledEmbeddingCount, Nat.card_eq_zero, or_iff_left (Finite.not_infinite inferInstance),
    isEmpty_subtype]
  simp [IndFree, isIndContained_iff_exists_iso_subgraph]

@[simp] lemma unlabeledEmbeddingCount_pos [Finite W] : 0 < H.unlabeledEmbeddingCount G ↔ G ⊴ H := by
  simp [Nat.pos_iff_ne_zero, unlabeledEmbeddingCount_eq_zero]

/-- There are at least as many induced labeled copies of `G` in `H` as there are induced
unlabeled ones. -/
lemma unlabeledEmbeddingCount_le_embeddingCount [Finite V] [Finite W] :
    H.unlabeledEmbeddingCount G ≤ H.embeddingCount G := by
  rw [unlabeledEmbeddingCount, embeddingCount]
  apply Nat.card_le_card_of_surjective
    (fun f : Embedding G H ↦ (⟨Embedding.toSubgraph f, f.toSubgraph_isInduced,
      ⟨f.toCopy.isoToSubgraph⟩⟩ : G.UnlabeledEmbedding H))
  rintro ⟨H', hInd, ⟨e⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : Embedding G H, Embedding.toSubgraph f = H' := by
    rw [← Set.mem_range, Embedding.range_toSubgraph]; exact ⟨hInd, ⟨e⟩⟩
  exact ⟨f, Subtype.ext hf⟩

private instance [IsEmpty V] : Nonempty (G.UnlabeledEmbedding H) :=
  let ⟨H', hInd, ⟨e⟩⟩ := (IsIndContained.of_isEmpty (G := G) (H := H)).exists_iso_subgraph
  ⟨⟨H', hInd, ⟨e⟩⟩⟩

private instance [IsEmpty V] : Subsingleton (G.UnlabeledEmbedding H) :=
  ⟨fun ⟨H', _, ⟨e⟩⟩ ⟨H'', _, ⟨e'⟩⟩ => Subtype.ext <|
    (H'.eq_bot_iff_verts_eq_empty.mpr (Set.isEmpty_coe_sort.mp e.toEquiv.symm.isEmpty)).trans
    (H''.eq_bot_iff_verts_eq_empty.mpr (Set.isEmpty_coe_sort.mp e'.toEquiv.symm.isEmpty)).symm⟩

@[simp] lemma unlabeledEmbeddingCount_of_isEmpty [IsEmpty V] (H : SimpleGraph W)
    (G : SimpleGraph V) : H.unlabeledEmbeddingCount G = 1 := Nat.card_unique

/-- Every induced unlabeled copy is an unlabeled copy. -/
lemma unlabeledEmbeddingCount_le_unlabeledCopyCount [Finite W] :
    H.unlabeledEmbeddingCount G ≤ H.unlabeledCopyCount G := by
  rw [unlabeledEmbeddingCount, unlabeledCopyCount_eq_nat_card]
  exact Nat.card_le_card_of_injective
    (fun H' : G.UnlabeledEmbedding H => (⟨H'.1, H'.2.2⟩ : G.UnlabeledCopy H))
    fun _ _ h => Subtype.ext (congrArg (·.1) h)

end UnlabeledEmbeddingCount

end SimpleGraph
