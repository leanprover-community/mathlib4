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

* `SimpleGraph.IsIsoSubgraph A B`, `A ⊑ B` is the relation that `B` contains a copy of `A`, that
  is, the type of copies of `A` in `B` is nonempty. This is equivalent to the existence of an
  isomorphism from `A` to a subgraph of `B`.

  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.

* `SimpleGraph.Free` is the predicate that `B` is `A`-free, that is, `B` does not contain a copy of
  `A`. This is the negation of `SimpleGraph.IsIsoSubgraph` implemented for convenience.
-/


open Fintype

namespace SimpleGraph

variable {V α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section Copy

/-- The type of copies as a subtype of *injective* homomorphisms. -/
abbrev Copy (A : SimpleGraph α) (B : SimpleGraph β) :=
  { f : A →g B // Function.Injective f }

/-- An injective homomorphism gives rise to a copy. -/
abbrev Hom.toCopy (f : A →g B) (h : Function.Injective f) : Copy A B := ⟨f, h⟩

/-- An embedding gives rise to a copy. -/
abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

/-- An isomorphism gives rise to a copy. -/
abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

/-- A copy gives rise to a homomorphism. -/
abbrev toHom : Copy A B → A →g B := Subtype.val

@[simp] lemma coe_toHom (f : Copy A B) : ⇑f.toHom = f := rfl

lemma injective : (f : Copy A B) → (Function.Injective f.toHom) := Subtype.prop

instance : FunLike (Copy A B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' _ _ h := Subtype.val_injective (DFunLike.coe_injective h)

@[simp] lemma coe_toHom_apply (f : Copy A B) (a : α) : ⇑f.toHom a = f a := rfl

/-- A copy induces an embedding of edge sets. -/
def mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where
  toFun := Hom.mapEdgeSet f.toHom
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
  exact Function.Injective.comp g.injective f.injective

@[simp]
theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/-- The copy from a subgraph to the supergraph. -/
def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) : Copy G₁ G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
theorem coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f := by ext; simp

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl

@[simp] theorem ofLE_refl : ofLE G G (le_refl G) = id G := by ext; simp

@[simp]
theorem ofLE_comp (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ≤ G₃) :
  (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/-- The copy from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G :=
  (Embedding.induce s).toCopy

end Copy

/-- A `Subgraph G` gives rise to a copy from the coercion to `G`. -/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G :=
  G'.hom.toCopy Subgraph.hom.injective

end Copy

section IsIsoSubgraph

/-- The relation `IsIsoSubgraph A B`, `A ⊑ B` says that `B` contains a copy of `A`.

This is equivalent to the existence of an isomorphism from `A` to a subgraph of `B`. -/
abbrev IsIsoSubgraph (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsIsoSubgraph

/-- A simple graph contains itself. -/
@[refl] theorem isIsoSubgraph_refl (G : SimpleGraph V) : G ⊑ G := ⟨Copy.id G⟩

/-- A simple graph contains its subgraphs. -/
theorem isIsoSubgraph_of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨Copy.ofLE G₁ G₂ h⟩

/-- If `A` contains `B` and `B` contains `C`, then `A` contains `C`. -/
theorem isIsoSubgraph_trans : A ⊑ B → B ⊑ C → A ⊑ C := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

alias IsIsoSubgraph.trans := isIsoSubgraph_trans

/-- If `B` contains `C` and `A` contains `B`, then `A` contains `C`. -/
theorem isIsoSubgraph_trans' : B ⊑ C → A ⊑ B → A ⊑ C := flip isIsoSubgraph_trans

alias IsIsoSubgraph.trans' := isIsoSubgraph_trans'

lemma IsIsoSubgraph.mono_right {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B ≤ B') : A ⊑ B' :=
  h_isub.trans <| isIsoSubgraph_of_le h_sub

alias IsIsoSubgraph.trans_le := IsIsoSubgraph.mono_right

lemma IsIsoSubgraph.mono_left {A' : SimpleGraph α} (h_sub : A ≤ A') (h_isub : A' ⊑ B) : A ⊑ B :=
  (isIsoSubgraph_of_le h_sub).trans h_isub

alias IsIsoSubgraph.trans_le' := IsIsoSubgraph.mono_left

/-- If `A ≃g B`, then `A` is contained in `C` if and only if `B` is contained in `C`. -/
theorem isIsoSubgraph_congr (e : A ≃g B) : A ⊑ C ↔ B ⊑ C :=
  ⟨isIsoSubgraph_trans ⟨e.symm.toCopy⟩, isIsoSubgraph_trans ⟨e.toCopy⟩⟩

/-- A simple graph having no vertices is contained in any simple graph. -/
lemma isIsoSubgraph_of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- A simple graph having no edges is contained in any simple graph having sufficent vertices. -/
theorem isIsoSubgraph_of_isEmpty_edgeSet [IsEmpty A.edgeSet] [Fintype α] [Fintype β]
    (h : card α ≤ card β) : A ⊑ B := by
  haveI := Function.Embedding.nonempty_of_card_le h
  let ι : α ↪ β := Classical.arbitrary (α ↪ β)
  exact ⟨⟨ι, isEmptyElim ∘ fun hadj ↦ (⟨s(_, _), hadj⟩ : A.edgeSet)⟩, ι.injective⟩

lemma bot_isIsoSubgraph (f : α ↪ β) : (⊥ : SimpleGraph α) ⊑ B := ⟨⟨f, False.elim⟩, f.injective⟩

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
lemma Subgraph.coe_isIsoSubgraph (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- The isomorphism from `Subgraph A` to its map under a copy `Copy A B`. -/
noncomputable def Subgraph.isoMap (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [map_verts, Equiv.Set.image_apply, coe_adj, map_adj, Relation.map_apply,
    Function.Injective.eq_iff f.injective, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
theorem isIsoSubgraph_iff_exists_iso_subgraph :
    A ⊑ B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) :=
  ⟨fun ⟨f⟩ ↦ ⟨Subgraph.map f.toHom ⊤, ⟨(Subgraph.isoMap f ⊤).comp Subgraph.topIso.symm⟩⟩,
    fun ⟨B', ⟨e⟩⟩ ↦ B'.coe_isIsoSubgraph.trans' ⟨e.toCopy⟩⟩

alias ⟨exists_iso_subgraph, _⟩ := isIsoSubgraph_iff_exists_iso_subgraph

end IsIsoSubgraph

section Free

/-- The proposition that a simple graph does not contain a copy of another simple graph. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

/-- If `A ≃g B`, then `C` is `A`-free if and only if `C` is `B`-free. -/
theorem free_congr (e : A ≃g B) : A.Free C ↔ B.Free C := by
  rw [not_iff_not]
  exact isIsoSubgraph_congr e

end Free

end SimpleGraph
