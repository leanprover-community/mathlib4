/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Set.Image

#align_import logic.embedding.set from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Interactions between embeddings and sets.

-/


universe u v w x

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

@[simp]
theorem Equiv.asEmbedding_range {α β : Sort _} {p : β → Prop} (e : α ≃ Subtype p) :
    Set.range e.asEmbedding = setOf p :=
  Set.ext fun x ↦ ⟨fun ⟨y, h⟩ ↦ h ▸ Subtype.coe_prop (e y), fun hs ↦ ⟨e.symm ⟨x, hs⟩, by simp⟩⟩
#align equiv.as_embedding_range Equiv.asEmbedding_range

end Equiv

namespace Function

namespace Embedding

/-- Embedding into `WithTop α`. -/
@[simps]
def coeWithTop {α} : α ↪ WithTop α :=
  { Embedding.some with toFun := WithTop.some }
#align function.embedding.coe_with_top Function.Embedding.coeWithTop
#align function.embedding.coe_with_top_apply Function.Embedding.coeWithTop_apply

/-- Given an embedding `f : α ↪ β` and a point outside of `Set.range f`, construct an embedding
`Option α ↪ β`. -/
@[simps]
def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β :=
  ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩
#align function.embedding.option_elim Function.Embedding.optionElim
#align function.embedding.option_elim_apply Function.Embedding.optionElim_apply

/-- Equivalence between embeddings of `Option α` and a sigma type over the embeddings of `α`. -/
@[simps]
def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ where
  toFun f := ⟨coeWithTop.trans f, f none, fun ⟨x, hx⟩ ↦ Option.some_ne_none x <| f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
  left_inv f := ext <| by rintro (_ | _) <;> simp [Option.coe_def]; rfl
  right_inv := fun ⟨f, y, hy⟩ ↦ by ext <;> simp [Option.coe_def]; rfl
#align function.embedding.option_embedding_equiv Function.Embedding.optionEmbeddingEquiv
#align function.embedding.option_embedding_equiv_apply_snd_coe Function.Embedding.optionEmbeddingEquiv_apply_snd_coe
#align function.embedding.option_embedding_equiv_symm_apply Function.Embedding.optionEmbeddingEquiv_symm_apply
#align function.embedding.option_embedding_equiv_apply_fst Function.Embedding.optionEmbeddingEquiv_apply_fst

/-- Restrict the codomain of an embedding. -/
def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a ↦ ⟨f a, H a⟩, fun _ _ h ↦ f.injective (congr_arg Subtype.val h)⟩
#align function.embedding.cod_restrict Function.Embedding.codRestrict

@[simp]
theorem codRestrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align function.embedding.cod_restrict_apply Function.Embedding.codRestrict_apply

open Set

/-- `Set.image` as an embedding `Set α ↪ Set β`. -/
@[simps apply]
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩
#align function.embedding.image Function.Embedding.image
#align function.embedding.image_apply Function.Embedding.image_apply

end Embedding

end Function

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply_coe]
def embeddingOfSubset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x ↦ ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ by
    congr
    injection h⟩
#align set.embedding_of_subset Set.embeddingOfSubset
#align set.embedding_of_subset_apply Set.embeddingOfSubset_apply_coeₓ

end Set

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`Disjoint p q`.

See also `Equiv.sumCompl`, for when `IsCompl p q`.  -/
@[simps apply]
def subtypeOrEquiv (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ { x // p x } ⊕ { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx ↦ (Or.inr hx : p x ∨ q x))
  left_inv x := by
    by_cases hx : p x
    · rw [subtypeOrLeftEmbedding_apply_left _ hx]
      simp [Subtype.ext_iff]
    · rw [subtypeOrLeftEmbedding_apply_right _ hx]
      simp [Subtype.ext_iff]
  right_inv x := by
    cases x with
    | inl x =>
        simp only [Sum.elim_inl]
        rw [subtypeOrLeftEmbedding_apply_left]
        · simp
        · simpa using x.prop
    | inr x =>
        simp only [Sum.elim_inr]
        rw [subtypeOrLeftEmbedding_apply_right]
        · simp
        · suffices ¬p x by simpa
          intro hp
          simpa using h.le_bot x ⟨hp, x.prop⟩
#align subtype_or_equiv subtypeOrEquiv
#align subtype_or_equiv_apply subtypeOrEquiv_apply

@[simp]
theorem subtypeOrEquiv_symm_inl (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // p x }) : (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.prop⟩ :=
  rfl
#align subtype_or_equiv_symm_inl subtypeOrEquiv_symm_inl

@[simp]
theorem subtypeOrEquiv_symm_inr (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // q x }) : (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.prop⟩ :=
  rfl
#align subtype_or_equiv_symm_inr subtypeOrEquiv_symm_inr

end Subtype
