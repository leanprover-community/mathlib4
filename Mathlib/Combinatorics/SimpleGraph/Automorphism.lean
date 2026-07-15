/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Combinatorics.SimpleGraph.InducedCopy
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Graph automorphisms

This file introduces the type `SimpleGraph.Aut G := G ≃g G` of graph automorphisms and the
associated count `SimpleGraph.autCount G`. The action of `Aut G` by precomposition on
`Copy G H` and `Embedding G H` is free, and its orbits are exactly the fibers of `toSubgraph`;
the orbit-stabiliser identities `copyCount = unlabeledCopyCount * autCount` and
`embeddingCount = unlabeledEmbeddingCount * autCount` follow.

## Main declarations

* `SimpleGraph.Aut G` and `SimpleGraph.autCount G`.
* `SimpleGraph.copyCount_eq_unlabeledCopyCount_mul_autCount`.
* `SimpleGraph.embeddingCount_eq_unlabeledEmbeddingCount_mul_autCount`.

## Implementation notes

`Aut G` is a transparent abbreviation for `G ≃g G` so that existing `RelIso` API applies
without unfolding. The count `autCount G` uses `Nat.card`, matching `copyCount` and its
companions; it is defined unconditionally and is zero when the automorphism group is infinite.
-/

public section

open Function

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### Automorphisms -/

/-- `G.Aut` is the type of graph automorphisms of `G`, namely `G ≃g G`. -/
abbrev Aut (G : SimpleGraph V) : Type _ := G ≃g G

instance : Nonempty G.Aut := ⟨Iso.refl⟩

instance [Finite V] : Finite G.Aut :=
  .of_injective (fun f ↦ (f.toEquiv : V ≃ V)) fun _ _ h ↦ RelIso.ext (Equiv.ext_iff.mp h)

variable (G) in
/-- `G.autCount` is the number of automorphisms of `G`, i.e. `Nat.card (G ≃g G)`. -/
noncomputable def autCount : ℕ := Nat.card G.Aut

lemma autCount_eq_nat_card (G : SimpleGraph V) : G.autCount = Nat.card G.Aut := by
  rw [autCount]

@[simp] lemma autCount_pos [Finite V] : 0 < G.autCount := Nat.card_pos

lemma one_le_autCount [Finite V] : 1 ≤ G.autCount := autCount_pos

/-! ### The action of `Aut G` on `Copy G H` -/

namespace Copy

lemma toSubgraph_comp_iso (f : Copy G H) (σ : G.Aut) :
    (f.comp σ.toCopy).toSubgraph = f.toSubgraph := by simp

lemma comp_toCopy_injective (f : Copy G H) :
    Injective fun σ : G.Aut ↦ f.comp σ.toCopy := fun σ₁ σ₂ h ↦ by
  ext v; simpa using DFunLike.congr_fun h v

/-- The unique automorphism of `G` relating two copies of `G` in `H` with the same image
subgraph. -/
@[expose] noncomputable def fiberAut (f₀ f : Copy G H) (h : f.toSubgraph = f₀.toSubgraph) :
    G.Aut := by
  refine ⟨equivOfToSubgraphEq h, fun {_ _} ↦ ?_⟩
  simp only [f₀.toSubgraph_adj_iff.symm, equivOfToSubgraphEq_apply, ← h, f.toSubgraph_adj_iff]

lemma fiberAut_spec (f₀ f : Copy G H) (h : f.toSubgraph = f₀.toSubgraph) :
    f = f₀.comp (fiberAut f₀ f h).toCopy := by
  ext v; simp [fiberAut]

/-- The fiber of `Copy.toSubgraph` over `f₀.toSubgraph` is equivalent to `Aut G`. -/
noncomputable def fiberEquivAut (f₀ : Copy G H) :
    {f : Copy G H // f.toSubgraph = f₀.toSubgraph} ≃ G.Aut where
  toFun f := fiberAut _ _ f.2
  invFun σ := ⟨f₀.comp σ.toCopy, toSubgraph_comp_iso _ _⟩
  left_inv _ := Subtype.ext (fiberAut_spec _ _ _).symm
  right_inv _ := comp_toCopy_injective _ (fiberAut_spec _ _ _).symm

/-- For each unlabelled copy `S` of `G` in `H`, the fiber of `Copy.toSubgraph` over `S.val` is
equivalent to `Aut G`. -/
noncomputable def fiberEquivAutOf (S : G.UnlabeledCopy H) :
    {f : Copy G H // f.toSubgraph = S.val} ≃ G.Aut :=
  S.toSubgraph_out ▸ fiberEquivAut S.out

/-- `Copy G H` decomposes as the dependent sum over unlabelled copies of `G` in `H`, with each
fiber the set of labelled copies sharing that image subgraph. -/
noncomputable def equivSigma :
    Copy G H ≃ Σ S : G.UnlabeledCopy H, {f : Copy G H // f.toSubgraph = S.val} where
  toFun f := ⟨f.toUnlabeledCopy, ⟨f, rfl⟩⟩
  invFun := fun ⟨_, f⟩ ↦ f.1
  left_inv _ := rfl
  right_inv := fun ⟨⟨S, hS⟩, ⟨f, hf⟩⟩ => by
    refine Sigma.ext (Subtype.ext hf) ?_
    exact (Subtype.heq_iff_coe_eq fun _ ↦ ⟨(·.trans hf), (·.trans hf.symm)⟩).mpr rfl

/-- **Orbit-stabiliser for copies (equivalence form).** Labelled copies of `G` in `H` are
canonically a product of unlabelled copies and automorphisms of `G`. -/
noncomputable def equivUnlabeledProdAut : Copy G H ≃ G.UnlabeledCopy H × G.Aut :=
  equivSigma.trans <| Equiv.sigmaEquivProdOfEquiv fiberEquivAutOf

end Copy

/-! ### The action of `Aut G` on `Embedding G H` -/

namespace Embedding

lemma toSubgraph_comp_iso (f : Embedding G H) (σ : G.Aut) :
    (f.comp σ.toEmbedding).toSubgraph = f.toSubgraph := by simp

lemma comp_toEmbedding_injective (f : Embedding G H) :
    Injective fun σ : G.Aut ↦ f.comp σ.toEmbedding := fun σ₁ σ₂ h ↦ by
  ext v; simpa using DFunLike.congr_fun h v

/-- The unique automorphism of `G` relating two embeddings of `G` in `H` with the same image
subgraph. -/
@[expose] noncomputable def fiberAut (f₀ f : Embedding G H) (h : f.toSubgraph = f₀.toSubgraph) :
    G.Aut := by
  refine ⟨equivOfToSubgraphEq h, fun {_ _} ↦ ?_⟩
  simp only [f₀.toSubgraph_adj_iff.symm, equivOfToSubgraphEq_apply, ← h, f.toSubgraph_adj_iff]

lemma fiberAut_spec (f₀ f : Embedding G H) (h : f.toSubgraph = f₀.toSubgraph) :
    f = f₀.comp (fiberAut f₀ f h).toEmbedding := by
  ext v; simp [fiberAut]

/-- The fiber of `Embedding.toSubgraph` over `f₀.toSubgraph` is equivalent to `Aut G`. -/
noncomputable def fiberEquivAut (f₀ : Embedding G H) :
    {f : Embedding G H // f.toSubgraph = f₀.toSubgraph} ≃ G.Aut where
  toFun f := fiberAut _ _ f.2
  invFun σ := ⟨f₀.comp σ.toEmbedding, toSubgraph_comp_iso _ _⟩
  left_inv _ := Subtype.ext (fiberAut_spec _ _ _).symm
  right_inv _ := comp_toEmbedding_injective _ (fiberAut_spec _ _ _).symm

/-- For each unlabelled induced copy `S` of `G` in `H`, the fiber of `Embedding.toSubgraph` over
`S.val` is equivalent to `Aut G`. -/
noncomputable def fiberEquivAutOf (S : G.UnlabeledEmbedding H) :
    {f : Embedding G H // f.toSubgraph = S.val} ≃ G.Aut :=
  S.toSubgraph_out ▸ fiberEquivAut S.out

/-- `Embedding G H` decomposes as the dependent sum over unlabelled induced copies of `G` in `H`,
with each fiber the set of labelled induced copies sharing that image subgraph. -/
noncomputable def equivSigma :
    Embedding G H ≃ Σ S : G.UnlabeledEmbedding H, {f : Embedding G H // f.toSubgraph = S.val} where
  toFun f := ⟨f.toUnlabeledEmbedding, ⟨f, rfl⟩⟩
  invFun := fun ⟨_, f⟩ ↦ f.1
  left_inv _ := rfl
  right_inv := fun ⟨⟨S, hS⟩, ⟨f, hf⟩⟩ => by
    refine Sigma.ext (Subtype.ext hf) ?_
    exact (Subtype.heq_iff_coe_eq fun _ ↦ ⟨(·.trans hf), (·.trans hf.symm)⟩).mpr rfl

/-- **Orbit-stabiliser for induced copies (equivalence form).** Induced labelled copies of `G`
in `H` are canonically a product of induced unlabelled copies and automorphisms of `G`. -/
noncomputable def equivUnlabeledProdAut : Embedding G H ≃ G.UnlabeledEmbedding H × G.Aut :=
  equivSigma.trans <| Equiv.sigmaEquivProdOfEquiv fiberEquivAutOf

end Embedding

/-! ### Multiplicative relations -/

/-- **Orbit-stabiliser for copies.** The number of labelled copies of `G` in `H` equals the
number of unlabelled copies times the number of automorphisms of `G`. -/
theorem copyCount_eq_unlabeledCopyCount_mul_autCount :
    H.copyCount G = H.unlabeledCopyCount G * G.autCount := by
  rw [copyCount_eq_nat_card, unlabeledCopyCount_eq_nat_card, autCount_eq_nat_card, ← Nat.card_prod]
  exact Nat.card_congr Copy.equivUnlabeledProdAut

/-- **Orbit-stabiliser for induced copies.** The number of induced labelled copies of `G` in `H`
equals the number of induced unlabelled copies times the number of automorphisms of `G`. -/
theorem embeddingCount_eq_unlabeledEmbeddingCount_mul_autCount :
    H.embeddingCount G = H.unlabeledEmbeddingCount G * G.autCount := by
  rw [embeddingCount_eq_nat_card, unlabeledEmbeddingCount_eq_nat_card,
      autCount_eq_nat_card, ← Nat.card_prod]
  exact Nat.card_congr Embedding.equivUnlabeledProdAut

end SimpleGraph
