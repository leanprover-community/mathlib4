/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Notation
import Mathlib.Order.SetNotation
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Pairwise
import Mathlib.Data.Set.Image

/-!
# Interactions between embeddings and sets.

-/

assert_not_exists WithTop

universe u v w x

open Set Set.Notation

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

@[simp]
theorem Equiv.asEmbedding_range {α β : Sort _} {p : β → Prop} (e : α ≃ Subtype p) :
    Set.range e.asEmbedding = setOf p :=
  Set.ext fun x ↦ ⟨fun ⟨y, h⟩ ↦ h ▸ Subtype.coe_prop (e y), fun hs ↦ ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

end Equiv

namespace Function

namespace Embedding

/-- Given an embedding `f : α ↪ β` and a point outside of `Set.range f`, construct an embedding
`Option α ↪ β`. -/
@[simps]
def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β :=
  ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

/-- Equivalence between embeddings of `Option α` and a sigma type over the embeddings of `α`. -/
@[simps]
def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ where
  toFun f := ⟨Embedding.some.trans f, f none, fun ⟨x, hx⟩ ↦ Option.some_ne_none x <| f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
  left_inv f := ext <| by rintro (_ | _) <;> simp [Option.coe_def]
  right_inv := fun ⟨f, y, hy⟩ ↦ by ext <;> simp [Option.coe_def]

/-- Restrict the codomain of an embedding. -/
def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a ↦ ⟨f a, H a⟩, fun _ _ h ↦ f.injective (congr_arg Subtype.val h)⟩

@[simp]
theorem codRestrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

open Set

/-- `Set.image` as an embedding `Set α ↪ Set β`. -/
@[simps apply]
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩

end Embedding

end Function

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply_coe]
def embeddingOfSubset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x ↦ ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ by
    congr
    injection h⟩

end Set

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`Disjoint p q`.

See also `Equiv.sumCompl`, for when `IsCompl p q`. -/
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

@[simp]
theorem subtypeOrEquiv_symm_inl (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // p x }) : (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.prop⟩ :=
  rfl

@[simp]
theorem subtypeOrEquiv_symm_inr (p q : α → Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // q x }) : (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.prop⟩ :=
  rfl

end Subtype

section Disjoint

variable {α ι : Type*} {s t r : Set α}

/-- For disjoint `s t : Set α`, the natural injection from `↑s ⊕ ↑t` to `α`. -/
@[simps] def Function.Embedding.sumSet (h : Disjoint s t) : s ⊕ t ↪ α where
  toFun := Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp [Subtype.val_inj]
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp [Subtype.val_inj]

@[norm_cast] lemma Function.Embedding.coe_sumSet (h : Disjoint s t) :
    (Function.Embedding.sumSet h : s ⊕ t → α) = Sum.elim (↑) (↑) := rfl

@[simp] theorem Function.Embedding.sumSet_preimage_inl (h : Disjoint s t) :
    .inl ⁻¹' (Function.Embedding.sumSet h ⁻¹' r) = r ∩ s := by
  simp [Set.ext_iff]

@[simp] theorem Function.Embedding.sumSet_preimage_inr (h : Disjoint s t) :
    .inr ⁻¹' (Function.Embedding.sumSet h ⁻¹' r) = r ∩ t := by
  simp [Set.ext_iff]

@[simp] theorem Function.Embedding.sumSet_range {s t : Set α} (h : Disjoint s t) :
    range (Function.Embedding.sumSet h) = s ∪ t := by
  simp [Set.ext_iff]

open scoped Function -- required for scoped `on` notation

/-- For an indexed family `s : ι → Set α` of disjoint sets,
the natural injection from the sigma-type `(i : ι) × ↑(s i)` to `α`. -/
@[simps] def Function.Embedding.sigmaSet {s : ι → Set α} (h : Pairwise (Disjoint on s)) :
    (i : ι) × s i ↪ α where
  toFun x := x.2.1
  inj' := by
    rintro ⟨i, x, hx⟩ ⟨j, -, hx'⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl

@[norm_cast] lemma Function.Embedding.coe_sigmaSet {s : ι → Set α} (h) :
    (Function.Embedding.sigmaSet h : ((i : ι) × s i) → α) = fun x ↦ x.2.1 := rfl

@[simp] theorem Function.Embedding.sigmaSet_preimage {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) (i : ι) (r : Set α) :
    Sigma.mk i ⁻¹' (Function.Embedding.sigmaSet h ⁻¹' r) = r ∩ s i := by
  simp [Set.ext_iff]

@[simp] theorem Function.Embedding.sigmaSet_range {s : ι → Set α}
    (h : Pairwise (Disjoint on s)) : Set.range (Function.Embedding.sigmaSet h) = ⋃ i, s i := by
  simp [Set.ext_iff]

end Disjoint
