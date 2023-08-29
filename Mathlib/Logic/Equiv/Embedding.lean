/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Logic.Embedding.Set

#align_import logic.equiv.embedding from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Equivalences on embeddings

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/


open Function.Embedding

namespace Equiv

/-- Embeddings from a sum type are equivalent to two separate embeddings with disjoint ranges. -/
def sumEmbeddingEquivProdEmbeddingDisjoint {α β γ : Type*} :
    (Sum α β ↪ γ) ≃ { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) } where
  toFun f :=
    ⟨(inl.trans f, inr.trans f), by
      rw [Set.disjoint_left]
      -- ⊢ ∀ ⦃a : γ⦄, a ∈ Set.range ↑(Function.Embedding.trans inl f, Function.Embeddin …
      rintro _ ⟨a, h⟩ ⟨b, rfl⟩
      -- ⊢ False
      simp only [trans_apply, inl_apply, inr_apply] at h
      -- ⊢ False
      have : Sum.inl a = Sum.inr b := f.injective h
      -- ⊢ False
      simp only at this⟩
      -- 🎉 no goals
  invFun := fun ⟨⟨f, g⟩, disj⟩ =>
    ⟨fun x =>
      match x with
      | Sum.inl a => f a
      | Sum.inr b => g b, by
      rintro (a₁ | b₁) (a₂ | b₂) f_eq <;>
        simp only [Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr] at f_eq
        -- ⊢ Sum.inl a₁ = Sum.inl a₂
        -- ⊢ Sum.inl a₁ = Sum.inr b₂
        -- ⊢ Sum.inr b₁ = Sum.inl a₂
        -- ⊢ Sum.inr b₁ = Sum.inr b₂
      · rw [f.injective f_eq]
        -- 🎉 no goals
      · exfalso
        -- ⊢ False
        refine disj.le_bot ⟨⟨a₁, f_eq⟩, ⟨b₂, by simp [f_eq]⟩⟩
        -- 🎉 no goals
      · exfalso
        -- ⊢ False
        exact disj.le_bot ⟨⟨a₂, rfl⟩, ⟨b₁, f_eq⟩⟩
        -- 🎉 no goals
      · rw [g.injective f_eq]⟩
        -- 🎉 no goals
  left_inv f := by
    dsimp only
    -- ⊢ {
    ext x
    -- ⊢ ↑{
    cases x <;> simp!
                -- 🎉 no goals
                -- 🎉 no goals
  right_inv := fun ⟨⟨f, g⟩, _⟩ => by
    simp only [Prod.mk.inj_iff]
    -- ⊢ {
    constructor
    -- 🎉 no goals
#align equiv.sum_embedding_equiv_prod_embedding_disjoint Equiv.sumEmbeddingEquivProdEmbeddingDisjoint

/-- Embeddings whose range lies within a set are equivalent to embeddings to that set.
This is `Function.Embedding.codRestrict` as an equiv. -/
def codRestrict (α : Type*) {β : Type*} (bs : Set β) :
    { f : α ↪ β // ∀ a, f a ∈ bs } ≃
      (α ↪ bs) where
  toFun f := (f : α ↪ β).codRestrict bs f.prop
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).prop⟩
  left_inv x := by ext; rfl
                   -- ⊢ ↑↑((fun f => { val := Function.Embedding.trans f (subtype fun x => x ∈ bs),  …
                        -- 🎉 no goals
  right_inv x := by ext; rfl
                    -- ⊢ ↑(↑((fun f => Function.Embedding.codRestrict bs ↑f (_ : ∀ (a : α), ↑↑f a ∈ b …
                         -- 🎉 no goals
#align equiv.cod_restrict Equiv.codRestrict

/-- Pairs of embeddings with disjoint ranges are equivalent to a dependent sum of embeddings,
in which the second embedding cannot take values in the range of the first. -/
def prodEmbeddingDisjointEquivSigmaEmbeddingRestricted {α β γ : Type*} :
    { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) } ≃
      Σf : α ↪ γ, β ↪ ↥(Set.range f)ᶜ :=
  (subtypeProdEquivSigmaSubtype fun (a : α ↪ γ) (b : β ↪ _) =>
        Disjoint (Set.range a) (Set.range b)).trans <|
    Equiv.sigmaCongrRight fun a =>
      (subtypeEquivProp <| by
            ext f
            -- ⊢ Disjoint (Set.range ↑a) (Set.range ↑f) ↔ ∀ (a_1 : β), ↑f a_1 ∈ (Set.range ↑a)ᶜ
            rw [← Set.range_subset_iff, Set.subset_compl_iff_disjoint_right, disjoint_comm]).trans
            -- 🎉 no goals
        (codRestrict _ _)
#align equiv.prod_embedding_disjoint_equiv_sigma_embedding_restricted Equiv.prodEmbeddingDisjointEquivSigmaEmbeddingRestricted

/-- A combination of the above results, allowing us to turn one embedding over a sum type
into two dependent embeddings, the second of which avoids any members of the range
of the first. This is helpful for constructing larger embeddings out of smaller ones. -/
def sumEmbeddingEquivSigmaEmbeddingRestricted {α β γ : Type*} :
    (Sum α β ↪ γ) ≃ Σf : α ↪ γ, β ↪ ↥(Set.range f)ᶜ :=
  Equiv.trans sumEmbeddingEquivProdEmbeddingDisjoint
    prodEmbeddingDisjointEquivSigmaEmbeddingRestricted
#align equiv.sum_embedding_equiv_sigma_embedding_restricted Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

/-- Embeddings from a single-member type are equivalent to members of the target type. -/
def uniqueEmbeddingEquivResult {α β : Type*} [Unique α] :
    (α ↪ β) ≃ β where
  toFun f := f default
  invFun x := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  left_inv _ := by
    ext x
    -- ⊢ ↑((fun x => { toFun := fun x_1 => x, inj' := (_ : ∀ (x_1 x_2 : α), (fun x_3  …
    simp_rw [Function.Embedding.coeFn_mk]
    -- ⊢ ↑x✝ default = ↑x✝ x
    congr 1
    -- ⊢ default = x
    exact Subsingleton.elim _ x
    -- 🎉 no goals
  right_inv _ := by simp
                    -- 🎉 no goals
#align equiv.unique_embedding_equiv_result Equiv.uniqueEmbeddingEquivResult

end Equiv
