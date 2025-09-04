/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Sum.Order
import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a disjoint union

This file provides the `LocallyFiniteOrder` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
-/


open Function Sum

namespace Finset

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

section SumLift₂

variable (f f₁ g₁ : α₁ → β₁ → Finset γ₁) (g f₂ g₂ : α₂ → β₂ → Finset γ₂)

/-- Lifts maps `α₁ → β₁ → Finset γ₁` and `α₂ → β₂ → Finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to `Alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp]
def sumLift₂ : ∀ (_ : α₁ ⊕ α₂) (_ : β₁ ⊕ β₂), Finset (γ₁ ⊕ γ₂)
  | inl a, inl b => (f a b).map Embedding.inl
  | inl _, inr _ => ∅
  | inr _, inl _ => ∅
  | inr a, inr b => (g a b).map Embedding.inr

variable {f f₁ g₁ g f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

theorem mem_sumLift₂ :
    c ∈ sumLift₂ f g a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁) ∨
        ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ := by
  constructor
  · rcases a with a | a <;> rcases b with b | b
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h ↦ (notMem_empty _ h).elim
    · refine fun h ↦ (notMem_empty _ h).elim
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h

theorem inl_mem_sumLift₂ {c₁ : γ₁} :
    inl c₁ ∈ sumLift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ := by
  rw [mem_sumLift₂, or_iff_left]
  · simp only [inl.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h

theorem inr_mem_sumLift₂ {c₂ : γ₂} :
    inr c₂ ∈ sumLift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ := by
  rw [mem_sumLift₂, or_iff_right]
  · simp only [inr.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h

theorem sumLift₂_eq_empty :
    sumLift₂ f g a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧
        ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor <;>
    · rintro a b rfl rfl
      exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)

theorem sumLift₂_nonempty :
    (sumLift₂ f g a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, exists_prop]

theorem sumLift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
    ∀ a b, sumLift₂ f₁ f₂ a b ⊆ sumLift₂ g₁ g₂ a b
  | inl _, inl _ => map_subset_map.2 (h₁ _ _)
  | inl _, inr _ => Subset.rfl
  | inr _, inl _ => Subset.rfl
  | inr _, inr _ => map_subset_map.2 (h₂ _ _)

end SumLift₂

section SumLexLift
variable (f₁ f₁' : α₁ → β₁ → Finset γ₁) (f₂ f₂' : α₂ → β₂ → Finset γ₂)
  (g₁ g₁' : α₁ → β₂ → Finset γ₁) (g₂ g₂' : α₁ → β₂ → Finset γ₂)

/-- Lifts maps `α₁ → β₁ → Finset γ₁`, `α₂ → β₂ → Finset γ₂`, `α₁ → β₂ → Finset γ₁`,
`α₂ → β₂ → Finset γ₂`  to a map `α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to
alternative monads if we can make sure to keep computability and universe polymorphism. -/
def sumLexLift : α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)
  | inl a, inl b => (f₁ a b).map Embedding.inl
  | inl a, inr b => (g₁ a b).disjSum (g₂ a b)
  | inr _, inl _ => ∅
  | inr a, inr b => (f₂ a b).map ⟨_, inr_injective⟩

@[simp]
lemma sumLexLift_inl_inl (a : α₁) (b : β₁) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inl b) = (f₁ a b).map Embedding.inl := rfl

@[simp]
lemma sumLexLift_inl_inr (a : α₁) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inr b) = (g₁ a b).disjSum (g₂ a b) := rfl

@[simp]
lemma sumLexLift_inr_inl (a : α₂) (b : β₁) : sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅ := rfl

@[simp]
lemma sumLexLift_inr_inr (a : α₂) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inr a) (inr b) = (f₂ a b).map ⟨_, inr_injective⟩ := rfl

variable {f₁ g₁ f₂ g₂ f₁' g₁' f₂' g₂'} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sumLexLift :
    c ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
        (∃ a₁ b₂ c₁, a = inl a₁ ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ ∈ g₁ a₁ b₂) ∨
          (∃ a₁ b₂ c₂, a = inl a₁ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
            ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ f₂ a₂ b₂ := by
  constructor
  · obtain a | a := a <;> obtain b | b := b
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h ↦ (mem_disjSum.1 h).elim ?_ ?_
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inr <| Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact fun h ↦ (notMem_empty _ h).elim
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr (Or.inr <| Or.inr <| ⟨a, b, c, rfl, rfl, rfl, hc⟩)
  · rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩ |
      ⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact mem_map_of_mem _ hc
    · exact inl_mem_disjSum.2 hc
    · exact inr_mem_disjSum.2 hc
    · exact mem_map_of_mem _ hc

lemma inl_mem_sumLexLift {c₁ : γ₁} :
    inl c₁ ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
        ∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₁ ∈ g₁ a₁ b₂ := by
  simp [mem_sumLexLift]

lemma inr_mem_sumLexLift {c₂ : γ₂} :
    inr c₂ ∈ sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ f₂ a₂ b₂ := by
  simp [mem_sumLexLift]

lemma sumLexLift_mono (hf₁ : ∀ a b, f₁ a b ⊆ f₁' a b) (hf₂ : ∀ a b, f₂ a b ⊆ f₂' a b)
    (hg₁ : ∀ a b, g₁ a b ⊆ g₁' a b) (hg₂ : ∀ a b, g₂ a b ⊆ g₂' a b) (a : α₁ ⊕ α₂)
    (b : β₁ ⊕ β₂) : sumLexLift f₁ f₂ g₁ g₂ a b ⊆ sumLexLift f₁' f₂' g₁' g₂' a b := by
  cases a <;> cases b
  exacts [map_subset_map.2 (hf₁ _ _), disjSum_mono (hg₁ _ _) (hg₂ _ _), Subset.rfl,
    map_subset_map.2 (hf₂ _ _)]

lemma sumLexLift_eq_empty :
    sumLexLift f₁ f₂ g₁ g₂ a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f₁ a₁ b₁ = ∅) ∧
        (∀ a₁ b₂, a = inl a₁ → b = inr b₂ → g₁ a₁ b₂ = ∅ ∧ g₂ a₁ b₂ = ∅) ∧
          ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → f₂ a₂ b₂ = ∅ := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ?_⟩
  any_goals rintro a b rfl rfl; exact map_eq_empty.1 h
  · rintro a b rfl rfl; exact disjSum_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · simp [h.2.1 _ _ rfl rfl]
  · rfl
  · exact map_eq_empty.2 (h.2.2 _ _ rfl rfl)

lemma sumLexLift_nonempty :
    (sumLexLift f₁ f₂ g₁ g₂ a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f₁ a₁ b₁).Nonempty) ∨
        (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ ((g₁ a₁ b₂).Nonempty ∨ (g₂ a₁ b₂).Nonempty)) ∨
          ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (f₂ a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLexLift_eq_empty, not_and_or, exists_prop, not_forall]

end SumLexLift
end Finset

open Finset

namespace Sum

variable {α β : Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

instance instLocallyFiniteOrder : LocallyFiniteOrder (α ⊕ β) where
  finsetIcc := sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

variable (a₁ a₂ : α) (b₁ b₂ : β)

theorem Icc_inl_inl : Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl :=
  rfl

theorem Ico_inl_inl : Ico (inl a₁ : α ⊕ β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl :=
  rfl

theorem Ioc_inl_inl : Ioc (inl a₁ : α ⊕ β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl :=
  rfl

theorem Ioo_inl_inl : Ioo (inl a₁ : α ⊕ β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl :=
  rfl

@[simp]
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ :=
  rfl

theorem Icc_inr_inr : Icc (inr b₁ : α ⊕ β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr :=
  rfl

theorem Ico_inr_inr : Ico (inr b₁ : α ⊕ β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr :=
  rfl

theorem Ioc_inr_inr : Ioc (inr b₁ : α ⊕ β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr :=
  rfl

theorem Ioo_inr_inr : Ioo (inr b₁ : α ⊕ β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr :=
  rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

instance : LocallyFiniteOrderBot (α ⊕ β) where
  finsetIic := Sum.elim (Iic · |>.map .inl) (Iic · |>.map .inr)
  finsetIio := Sum.elim (Iio · |>.map .inl) (Iio · |>.map .inr)
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)

theorem Iic_inl : Iic (inl a : α ⊕ β) = (Iic a).map Embedding.inl := rfl
theorem Iic_inr : Iic (inr b : α ⊕ β) = (Iic b).map Embedding.inr := rfl
theorem Iio_inl : Iio (inl a : α ⊕ β) = (Iio a).map Embedding.inl := rfl
theorem Iio_inr : Iio (inr b : α ⊕ β) = (Iio b).map Embedding.inr := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]

instance : LocallyFiniteOrderTop (α ⊕ β) where
  finsetIci := Sum.elim (Ici · |>.map .inl) (Ici · |>.map .inr)
  finsetIoi := Sum.elim (Ioi · |>.map .inl) (Ioi · |>.map .inr)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)

theorem Ici_inl : Ici (inl a : α ⊕ β) = (Ici a).map Embedding.inl := rfl
theorem Ici_inr : Ici (inr b : α ⊕ β) = (Ici b).map Embedding.inr := rfl
theorem Ioi_inl : Ioi (inl a : α ⊕ β) = (Ioi a).map Embedding.inl := rfl
theorem Ioi_inr : Ioi (inr b : α ⊕ β) = (Ioi b).map Embedding.inr := rfl

end LocallyFiniteOrderTop

end Disjoint

/-! ### Lexicographical sum of orders -/

namespace Lex

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot β]

/-- Throwaway tactic. -/
local elab "simp_lex" : tactic => do
  Lean.Elab.Tactic.evalTactic <| ← `(tactic|
    refine toLex.surjective.forall₃.2 ?_;
    rintro (a | a) (b | b) (c | c) <;> simp)

instance locallyFiniteOrder : LocallyFiniteOrder (α ⊕ₗ β) where
  finsetIcc a b :=
    (sumLexLift Icc Icc (fun a _ => Ici a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIco a b :=
    (sumLexLift Ico Ico (fun a _ => Ici a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoc a b :=
    (sumLexLift Ioc Ioc (fun a _ => Ioi a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoo a b :=
    (sumLexLift Ioo Ioo (fun a _ => Ioi a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finset_mem_Icc := by simp_lex
  finset_mem_Ico := by simp_lex
  finset_mem_Ioc := by simp_lex
  finset_mem_Ioo := by simp_lex

variable (a a₁ a₂ : α) (b b₁ b₂ : β)

lemma Icc_inl_inl :
    Icc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Icc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ico_inl_inl :
    Ico (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ico a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ioc_inl_inl :
    Ioc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ioo_inl_inl :
    Ioo (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

@[simp]
lemma Icc_inl_inr : Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
lemma Ico_inl_inr : Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
lemma Ioc_inl_inr : Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
lemma Ioo_inl_inr : Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
lemma Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
lemma Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
lemma Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
lemma Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅ := rfl

lemma Icc_inr_inr :
    Icc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Icc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ico_inr_inr :
    Ico (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ico b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ioc_inr_inr :
    Ioc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

lemma Ioo_inr_inr :
    Ioo (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [Fintype α] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (α ⊕ₗ β) where
  finsetIic := Sum.elim
    (Iic · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iic x) |>.map toLex.toEmbedding) ∘ ofLex
  finsetIio := Sum.elim
    (Iio · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iio x) |>.map toLex.toEmbedding) ∘ ofLex
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)

lemma Iic_inl : Iic (inlₗ a : α ⊕ₗ β) = (Iic a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
lemma Iic_inr : Iic (inrₗ b : α ⊕ₗ β) = (Finset.univ.disjSum (Iic b)).map toLex.toEmbedding := rfl

lemma Iio_inl : Iio (inlₗ a : α ⊕ₗ β) = (Iio a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
lemma Iio_inr : Iio (inrₗ b : α ⊕ₗ β) = (Finset.univ.disjSum (Iio b)).map toLex.toEmbedding := rfl

end LocallyFiniteOrderBot

/-- TODO: `LocallyFiniteOrder.toLocallyFiniteOrderBot` is probably a bad instance, as it forms
a diamond with this instance, and constructs data from data. We should consider removing it. -/
example [Fintype α] [Preorder α] [Preorder β] [OrderBot α] [OrderBot β] [OrderTop α]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] :
    LocallyFiniteOrder.toLocallyFiniteOrderBot = instLocallyFiniteOrderBot (α := α) (β := β) := by
  try with_reducible_and_instances rfl -- fails
  try rfl -- fails
  exact Subsingleton.elim _ _

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [Fintype β] [LocallyFiniteOrderTop β]

instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α ⊕ₗ β) where
  finsetIci := Sum.elim
    (fun x => (Ici x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ici · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finsetIoi := Sum.elim
    (fun x => (Ioi x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ioi · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)

lemma Ici_inl : Ici (inlₗ a : α ⊕ₗ β) = ((Ici a).disjSum Finset.univ).map toLex.toEmbedding := rfl
lemma Ici_inr : Ici (inrₗ b : α ⊕ₗ β) = (Ici b).map (Embedding.inr.trans toLex.toEmbedding) := rfl

lemma Ioi_inl : Ioi (inlₗ a : α ⊕ₗ β) = ((Ioi a).disjSum Finset.univ).map toLex.toEmbedding := rfl
lemma Ioi_inr : Ioi (inrₗ b : α ⊕ₗ β) = (Ioi b).map (Embedding.inr.trans toLex.toEmbedding) := rfl

end LocallyFiniteOrderTop

end Lex
end Sum
