/-
Copyright (c) 2022 Joanna Choules. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joanna Choules
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Homomorphisms from finite subgraphs

This file defines the type of finite subgraphs of a `SimpleGraph` and proves a compactness result
for homomorphisms to a finite codomain.

## Main statements

* `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`: If every finite subgraph of a (possibly
  infinite) graph `G` has a homomorphism to some finite graph `F`, then there is also a homomorphism
  `G →g F`.

## Notations

`→fg` is a module-local variant on `→g` where the domain is a finite subgraph of some supergraph
`G`.

## Implementation notes

The proof here uses compactness as formulated in `nonempty_sections_of_finite_inverse_system`. For
finite subgraphs `G'' ≤ G'`, the inverse system `finsubgraphHomFunctor` restricts homomorphisms
`G' →fg F` to domain `G''`.
-/


open Set CategoryTheory

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {F : SimpleGraph W}

namespace SimpleGraph

/-- The subtype of `G.subgraph` comprising those subgraphs with finite vertex sets. -/
abbrev Finsubgraph (G : SimpleGraph V) :=
  { G' : G.Subgraph // G'.verts.Finite }

/-- A graph homomorphism from a finite subgraph of G to F. -/
abbrev FinsubgraphHom (G' : G.Finsubgraph) (F : SimpleGraph W) :=
  G'.val.coe →g F

local infixl:50 " →fg " => FinsubgraphHom

namespace Finsubgraph

instance : OrderBot G.Finsubgraph where
  bot := ⟨⊥, finite_empty⟩
  bot_le _ := bot_le (α := G.Subgraph)

instance : Sup G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, G₁.2.union G₂.2⟩⟩

instance : Inf G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, G₁.2.subset inter_subset_left⟩⟩

instance instSDiff : SDiff G.Finsubgraph where
  sdiff G₁ G₂ := ⟨G₁ \ G₂, G₁.2.subset (Subgraph.verts_mono sdiff_le)⟩

@[simp, norm_cast] lemma coe_bot : (⊥ : G.Finsubgraph) = (⊥ : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph) := rfl

instance instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra G.Finsubgraph :=
  Subtype.coe_injective.generalizedCoheytingAlgebra _ coe_sup coe_inf coe_bot coe_sdiff

section Finite
variable [Finite V]

instance instTop : Top G.Finsubgraph where top := ⟨⊤, finite_univ⟩
instance instHasCompl : HasCompl G.Finsubgraph where compl G' := ⟨G'ᶜ, Set.toFinite _⟩
instance instHNot : HNot G.Finsubgraph where hnot G' := ⟨￢G', Set.toFinite _⟩
instance instHImp : HImp G.Finsubgraph where himp G₁ G₂ := ⟨G₁ ⇨ G₂, Set.toFinite _⟩
instance instSupSet : SupSet G.Finsubgraph where sSup s := ⟨⨆ G ∈ s, ↑G, Set.toFinite _⟩
instance instInfSet : InfSet G.Finsubgraph where sInf s := ⟨⨅ G ∈ s, ↑G, Set.toFinite _⟩

@[simp, norm_cast] lemma coe_top : (⊤ : G.Finsubgraph) = (⊤ : G.Subgraph) := rfl
@[simp, norm_cast] lemma coe_compl (G' : G.Finsubgraph) : ↑(G'ᶜ) = (G'ᶜ : G.Subgraph) := rfl
@[simp, norm_cast] lemma coe_hnot (G' : G.Finsubgraph) : ↑(￢G') = (￢G' : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_himp (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_sSup (s : Set G.Finsubgraph) : sSup s = (⨆ G ∈ s, G : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_sInf (s : Set G.Finsubgraph) : sInf s = (⨅ G ∈ s, G : G.Subgraph) := rfl

@[simp, norm_cast]
lemma coe_iSup {ι : Sort*} (f : ι → G.Finsubgraph) : ⨆ i, f i = (⨆ i, f i : G.Subgraph) := by
  rw [iSup, coe_sSup, iSup_range]

@[simp, norm_cast]
lemma coe_iInf {ι : Sort*} (f : ι → G.Finsubgraph) : ⨅ i, f i = (⨅ i, f i : G.Subgraph) := by
  rw [iInf, coe_sInf, iInf_range]

instance instCompletelyDistribLattice : CompletelyDistribLattice G.Finsubgraph :=
  Subtype.coe_injective.completelyDistribLattice _ coe_sup coe_inf coe_sSup coe_sInf coe_top coe_bot
    coe_compl coe_himp coe_hnot coe_sdiff

end Finite
end Finsubgraph

/-- The finite subgraph of G generated by a single vertex. -/
def singletonFinsubgraph (v : V) : G.Finsubgraph :=
  ⟨SimpleGraph.singletonSubgraph _ v, by simp⟩

/-- The finite subgraph of G generated by a single edge. -/
def finsubgraphOfAdj {u v : V} (e : G.Adj u v) : G.Finsubgraph :=
  ⟨SimpleGraph.subgraphOfAdj _ e, by simp⟩

-- Lemmas establishing the ordering between edge- and vertex-generated subgraphs.
theorem singletonFinsubgraph_le_adj_left {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph u ≤ finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

theorem singletonFinsubgraph_le_adj_right {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph v ≤ finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

/-- Given a homomorphism from a subgraph to `F`, construct its restriction to a sub-subgraph. -/
def FinsubgraphHom.restrict {G' G'' : G.Finsubgraph} (h : G'' ≤ G') (f : G' →fg F) : G'' →fg F := by
  refine ⟨fun ⟨v, hv⟩ => f.toFun ⟨v, h.1 hv⟩, ?_⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  exact f.map_rel' (h.2 huv)

/-- The inverse system of finite homomorphisms. -/
def finsubgraphHomFunctor (G : SimpleGraph V) (F : SimpleGraph W) :
    G.Finsubgraphᵒᵖ ⥤ Type max u v where
  obj G' := G'.unop →fg F
  map g f := f.restrict (CategoryTheory.leOfHom g.unop)

/-- If every finite subgraph of a graph `G` has a homomorphism to a finite graph `F`, then there is
a homomorphism from the whole of `G` to `F`. -/
theorem nonempty_hom_of_forall_finite_subgraph_hom [Finite W]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g F) : Nonempty (G →g F) := by
  -- Obtain a `Fintype` instance for `W`.
  cases nonempty_fintype W
  -- Establish the required interface instances.
  haveI : ∀ G' : G.Finsubgraphᵒᵖ, Nonempty ((finsubgraphHomFunctor G F).obj G') := fun G' =>
    ⟨h G'.unop G'.unop.property⟩
  haveI : ∀ G' : G.Finsubgraphᵒᵖ, Fintype ((finsubgraphHomFunctor G F).obj G') := by
    intro G'
    haveI : Fintype (G'.unop.val.verts : Type u) := G'.unop.property.fintype
    haveI : Fintype (↥G'.unop.val.verts → W) := by classical exact Pi.fintype
    exact Fintype.ofInjective (fun f => f.toFun) RelHom.coe_fn_injective
  -- Use compactness to obtain a section.
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (finsubgraphHomFunctor G F)
  refine ⟨⟨fun v => ?_, ?_⟩⟩
  · -- Map each vertex using the homomorphism provided for its singleton subgraph.
    exact
      (u (Opposite.op (singletonFinsubgraph v))).toFun
        ⟨v, by
          unfold singletonFinsubgraph
          simp⟩
  · -- Prove that the above mapping preserves adjacency.
    intro v v' e
    simp only
    /- The homomorphism for each edge's singleton subgraph agrees with those for its source and
        target vertices. -/
    have hv : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v) :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_left)
    have hv' : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v') :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_right)
    rw [← hu hv, ← hu hv']
    -- Porting note: was `apply Hom.map_adj`
    refine Hom.map_adj (u (Opposite.op (finsubgraphOfAdj e))) ?_
    -- `v` and `v'` are definitionally adjacent in `finsubgraphOfAdj e`
    simp [finsubgraphOfAdj]

end SimpleGraph
