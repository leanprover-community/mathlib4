/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Copies of Simple Graphs

This file introduces the concept of one simple graph containing a copy of another.

## Main definitions

* `SimpleGraph.Copy A B` is the type of copies of `A` in `B`, implemented as the subtype of
  *injective* homomorphisms.

* `SimpleGraph.IsContained A B`, `A ⊑ B` is the relation that `B` contains a copy of `A`, that
  is, the type of copies of `A` in `B` is nonempty. This is equivalent to the existence of an
  isomorphism from `A` to a subgraph of `B`.

  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.

* `SimpleGraph.Free` is the predicate that `B` is `A`-free, that is, `B` does not contain a copy of
  `A`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.

## Notation

The following notation is declared in locale `SimpleGraph`:

* `G ⊑ H` for `SimpleGraph.IsContained G H`.
-/

open Finset Function

namespace SimpleGraph
variable {V W X α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

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

@[deprecated (since := "2025-03-19")] alias coe_toHom_apply := toHom_apply

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

instance [Subsingleton (V → W)] : Subsingleton (G.Copy H) := DFunLike.coe_injective.subsingleton

instance [Fintype {f : G →g H // Injective f}] : Fintype (G.Copy H) :=
  .ofEquiv {f : G →g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }

end Copy

/-- A `Subgraph G` gives rise to a copy from the coercion to `G`. -/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G := G'.hom.toCopy hom_injective

end Copy

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

lemma isContained_congr_left (e₁ : A ≃g B) : A ⊑ C ↔ B ⊑ C := isContained_congr e₁ Iso.refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

lemma isContained_congr_right (e₂ : B ≃g C) : A ⊑ B ↔ A ⊑ C := isContained_congr Iso.refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

/-- A simple graph having no vertices is contained in any simple graph. -/
lemma IsContained.of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- `⊥` is contained in any simple graph having sufficently many vertices. -/
lemma bot_isContained_iff_card_le [Fintype α] [Fintype β] :
    (⊥ : SimpleGraph α) ⊑ B ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨f⟩ ↦ Fintype.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- The isomorphism from `Subgraph A` to its map under a copy `Copy A B`. -/
noncomputable def Subgraph.Copy.map (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [map_verts, Equiv.Set.image_apply, coe_adj, map_adj, Relation.map_apply,
    Function.Injective.eq_iff f.injective, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
theorem isContained_iff_exists_iso_subgraph :
    A ⊑ B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) :=
  ⟨fun ⟨f⟩ ↦ ⟨Subgraph.map f.toHom ⊤, ⟨(Subgraph.Copy.map f ⊤).comp Subgraph.topIso.symm⟩⟩,
    fun ⟨B', ⟨e⟩⟩ ↦ B'.coe_isContained.trans' ⟨e.toCopy⟩⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

end IsContained

section Free

/-- The proposition that a simple graph does not contain a copy of another simple graph. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

lemma not_free : ¬A.Free B ↔ A ⊑ B := not_not

/-- If `A ≃g H` and `B ≃g G` then `B` is `A`-free if and only if `G` is `H`-free. -/
theorem free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free B ↔ H.Free G :=
  (isContained_congr e₁ e₂).not

lemma free_congr_left (e₁ : A ≃g B) : A.Free C ↔ B.Free C := free_congr e₁ Iso.refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

lemma free_congr_right (e₂ : B ≃g C) : A.Free B ↔ A.Free C := free_congr Iso.refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

lemma free_bot (h : A ≠ ⊥) : A.Free (⊥ : SimpleGraph β) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.not_mem_empty (h.choose.map f)

end Free

end SimpleGraph
