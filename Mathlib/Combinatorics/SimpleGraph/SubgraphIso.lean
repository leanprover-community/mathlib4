/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Subgraph isomorphism

This file defines subgraph isomorphisms for simple graphs.

## Main definitions

* `SimpleGraph.SubgraphIso A B`, `A ≲g B` is the type of subgraph isomorphisms from `A` to `B`,
  implemented as the subtype of *injective* homomorphisms.

  It is standard to define a subgraph isomorphism as an isomorphism from `A` to a subgraph of `B`.
  However, `SimpleGraph.IsSubgraph` is such that subgraphs of `B` have the same number of vertices
  as `B`. In this case, it is impossible to have a subgraph isomorphism from `A` to `B` using
  `SimpleGraph.IsSubgraph` unless `A` and `B` have the same number of vertices. It is for this
  reason that the mathematically equivalent definition of a subgraph isomorphism as an *injective*
  homomorphism is taken.

* `SimpleGraph.IsIsoSubgraph` is the relation that `B` contains a copy of `A`, that
  is, `A` is an isomorphic subgraph of `B`, that is, the type of subgraph isomorphisms from `A` to
  `B` is nonempty.

  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.

* `SimpleGraph.Free` is the predicate that `B` is `A`-free, that is, `B` does not contain a copy of
  `A`. This is the negation of `SimpleGraph.IsIsoSubgraph` implemented for convenience.
-/


open Fintype

namespace SimpleGraph

variable {V α β γ : Type*} {G : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section SubgraphIso

/-- The type of subgraph isomorphisms as a subtype of *injective* homomorphisms.

The notation `A ≲g B` is introduced for the type of subgrah isomorphisms. -/
abbrev SubgraphIso (A : SimpleGraph α) (B : SimpleGraph β) :=
  { f : A →g B // Function.Injective f }

@[inherit_doc] infixl:50 " ≲g " => SubgraphIso

/-- An injective homomorphism gives rise to a subgraph isomorphism. -/
abbrev Hom.toSubgraphIso (f : A →g B) (h : Function.Injective f) : A ≲g B := ⟨f, h⟩

/-- An embedding gives rise to a subgraph isomorphism. -/
abbrev Embedding.toSubgraphIso (f : A ↪g B) : A ≲g B := Hom.toSubgraphIso f.toHom f.injective

/-- An isomorphism gives rise to a subgraph isomorphism. -/
abbrev Iso.toSubgraphIso (f : A ≃g B) : A ≲g B := Embedding.toSubgraphIso f.toEmbedding

namespace SubgraphIso

/-- A subgraph isomorphism gives rise to a homomorphism. -/
abbrev toHom : A ≲g B → A →g B := Subtype.val

@[simp] lemma coe_toHom (f : A ≲g B) : ⇑f.toHom = f := rfl

lemma injective : (f : A ≲g B) → (Function.Injective f.toHom) := Subtype.prop

instance : FunLike (A ≲g B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' _ _ h := Subtype.val_injective (DFunLike.coe_injective h)

@[simp] lemma coe_toHom_apply (f : A ≲g B) (a : α) : ⇑f.toHom a = f a := rfl

/-- A subgraph isomorphism induces an embedding of edge sets. -/
def mapEdgeSet (f : A ≲g B) : A.edgeSet ↪ B.edgeSet where
  toFun := Hom.mapEdgeSet f.toHom
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A subgraph isomorphisms induces an embedding of neighbor sets. -/
def mapNeighborSet (f : A ≲g B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- A subgraph isomorphism gives rise to an embedding of vertex types. -/
def asEmbedding (f : A ≲g B) : α ↪ β := ⟨f, f.injective⟩

/-- The identity subgraph isomorphism from a simple graph to itself. -/
@[refl] def refl (G : SimpleGraph V) : G ≲g G := ⟨Hom.id, Function.injective_id⟩

/-- The subgraph isomorphism from a subgraph to the supergraph. -/
def ofLE {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : G₁ ≲g G₂ :=
  ⟨Hom.ofLE h, Function.injective_id⟩

/-- The subgraph isomorphism from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : (G.induce s) ≲g G :=
  (Embedding.induce s).toSubgraphIso

/-- The composition of subgraph isomorphisms is a subgraph isomorphism. -/
def comp (g : B ≲g C) (f : A ≲g B) : A ≲g C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact Function.Injective.comp g.injective f.injective

@[simp]
theorem comp_apply (g : B ≲g C) (f : A ≲g B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

end SubgraphIso

/-- The subgraph isomorphism from a `Subgraph G` coercion to `G`. -/
def Subgraph.subgraphIso (G' : G.Subgraph) : (G'.coe) ≲g G :=
  G'.hom.toSubgraphIso Subgraph.hom.injective

end SubgraphIso

section IsIsoSubgraph

/-- The relation that a simple graph contains a copy of a simple graph. -/
abbrev IsIsoSubgraph (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (A ≲g B)

/-- A simple graph contains itself. -/
@[refl]
theorem isIsoSubgraph_refl (G : SimpleGraph V) :
  G.IsIsoSubgraph G := ⟨SubgraphIso.refl G⟩

/-- A simple graph contains its subgraphs. -/
theorem isIsoSubgraph_of_le {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) :
  G₁.IsIsoSubgraph G₂ := ⟨SubgraphIso.ofLE h⟩

/-- If `A` contains `B` and `B` contains `C`, then `A` contains `C`. -/
theorem isIsoSubgraph_trans : A.IsIsoSubgraph B → B.IsIsoSubgraph C → A.IsIsoSubgraph C :=
  fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

alias IsIsoSubgraph.trans := isIsoSubgraph_trans

/-- If `B` contains `C` and `A` contains `B`, then `A` contains `C`. -/
theorem isIsoSubgraph_trans' : B.IsIsoSubgraph C → A.IsIsoSubgraph B → A.IsIsoSubgraph C :=
  flip isIsoSubgraph_trans

alias IsIsoSubgraph.trans' := isIsoSubgraph_trans'

/-- A simple graph having no vertices is contained in any simple graph. -/
theorem isIsoSubgraph_of_isEmpty [IsEmpty α] : A.IsIsoSubgraph B := by
  let ι : α ↪ β := Function.Embedding.ofIsEmpty
  let f : A →g B := ⟨ι, by apply isEmptyElim⟩
  exact ⟨f.toSubgraphIso ι.injective⟩

/-- A simple graph having no edges is contained in any simple graph having sufficent vertices. -/
theorem isIsoSubgraph_of_isEmpty_edgeSet [IsEmpty A.edgeSet] [Fintype α] [Fintype β]
    (h : card α ≤ card β) : A.IsIsoSubgraph B := by
  haveI : Nonempty (α ↪ β) := Function.Embedding.nonempty_of_card_le h
  let ι : α ↪ β := Classical.arbitrary (α ↪ β)
  let f : A →g B := by
    use ι
    intro a₁ a₂ hadj
    let e : A.edgeSet := by
      use s(a₁, a₂)
      rw [mem_edgeSet]
      exact hadj
    exact isEmptyElim e
  exact ⟨f.toSubgraphIso ι.injective⟩

/-- If `A ≃g B`, then `A` is contained in `C` if and only if `B` is contained in `C`. -/
theorem isIsoSubgraph_iff_of_iso (f : A ≃g B) :
    A.IsIsoSubgraph C ↔ B.IsIsoSubgraph C :=
  ⟨isIsoSubgraph_trans ⟨f.symm.toSubgraphIso⟩, isIsoSubgraph_trans ⟨f.toSubgraphIso⟩⟩

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
lemma Subgraph.coe_isIsoSubgraph (G' : G.Subgraph) : (G'.coe).IsIsoSubgraph G := ⟨G'.subgraphIso⟩

/-- The isomorphism from `Subgraph A` to its map under a subgraph isomorphism `A ≲g B`. -/
noncomputable def Subgraph.isoMap (f : A ≲g B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [map_verts, Equiv.Set.image_apply, coe_adj, map_adj, Relation.map_apply,
    Function.Injective.eq_iff f.injective, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
theorem isIsoSubgraph_iff_exists_iso_subgraph :
    A.IsIsoSubgraph B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) := by
  constructor
  · intro ⟨f⟩
    use (⊤ : A.Subgraph).map f
    exact ⟨((⊤ : A.Subgraph).isoMap f).comp Subgraph.topIso.symm⟩
  · intro ⟨B', ⟨e⟩⟩
    exact B'.coe_isIsoSubgraph.trans' ⟨e.toSubgraphIso⟩

alias ⟨exists_iso_subgraph, _⟩ := isIsoSubgraph_iff_exists_iso_subgraph

end IsIsoSubgraph

section Free

/-- The proposition that a simple graph does not contain a copy of another simple graph. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A.IsIsoSubgraph B

/-- If `A ≃g B`, then `C` is `A`-free if and only if `C` is `B`-free. -/
theorem free_iff_of_iso (f : A ≃g B) :
    A.Free C ↔ B.Free C := by
  rw [not_iff_not]
  exact isIsoSubgraph_iff_of_iso f

end Free

end SimpleGraph
