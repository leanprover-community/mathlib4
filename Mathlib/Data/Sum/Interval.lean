/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Sum.Order
import Mathlib.Order.LocallyFinite

#align_import data.sum.interval from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!
# Finite intervals in a disjoint union

This file provides the `LocallyFiniteOrder` instance for the disjoint sum of two orders.

## TODO

Do the same for the lexicographic sum of orders.
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
def sumLift₂ : ∀ (_ : Sum α₁ α₂) (_ : Sum β₁ β₂), Finset (Sum γ₁ γ₂)
  | inl a, inl b => (f a b).map Embedding.inl
  | inl _, inr _ => ∅
  | inr _, inl _ => ∅
  | inr a, inr b => (g a b).map Embedding.inr
#align finset.sum_lift₂ Finset.sumLift₂

variable {f f₁ g₁ g f₂ g₂} {a : Sum α₁ α₂} {b : Sum β₁ β₂} {c : Sum γ₁ γ₂}

theorem mem_sumLift₂ :
    c ∈ sumLift₂ f g a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁) ∨
        ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ := by
  constructor
  -- ⊢ c ∈ sumLift₂ f g a b → (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c …
  · cases' a with a a <;> cases' b with b b
    -- ⊢ c ∈ sumLift₂ f g (inl a) b → (∃ a₁ b₁ c₁, inl a = inl a₁ ∧ b = inl b₁ ∧ c =  …
                          -- ⊢ c ∈ sumLift₂ f g (inl a) (inl b) → (∃ a₁ b₁ c₁, inl a = inl a₁ ∧ inl b = inl …
                          -- ⊢ c ∈ sumLift₂ f g (inr a) (inl b) → (∃ a₁ b₁ c₁, inr a = inl a₁ ∧ inl b = inl …
    · rw [sumLift₂, mem_map]
      -- ⊢ (∃ a_1, a_1 ∈ f a b ∧ ↑Embedding.inl a_1 = c) → (∃ a₁ b₁ c₁, inl a = inl a₁  …
      rintro ⟨c, hc, rfl⟩
      -- ⊢ (∃ a₁ b₁ c₁, inl a = inl a₁ ∧ inl b = inl b₁ ∧ ↑Embedding.inl c = inl c₁ ∧ c …
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
      -- 🎉 no goals
    · refine' fun h ↦ (not_mem_empty _ h).elim
      -- 🎉 no goals
    · refine' fun h ↦ (not_mem_empty _ h).elim
      -- 🎉 no goals
    · rw [sumLift₂, mem_map]
      -- ⊢ (∃ a_1, a_1 ∈ g a b ∧ ↑Embedding.inr a_1 = c) → (∃ a₁ b₁ c₁, inr a = inl a₁  …
      rintro ⟨c, hc, rfl⟩
      -- ⊢ (∃ a₁ b₁ c₁, inr a = inl a₁ ∧ inr b = inl b₁ ∧ ↑Embedding.inr c = inl c₁ ∧ c …
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
      -- 🎉 no goals
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h
    -- ⊢ inl c ∈ sumLift₂ f g (inl a) (inl b)
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align finset.mem_sum_lift₂ Finset.mem_sumLift₂

theorem inl_mem_sumLift₂ {c₁ : γ₁} :
    inl c₁ ∈ sumLift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ := by
  rw [mem_sumLift₂, or_iff_left]
  -- ⊢ (∃ a₁ b₁ c₁_1, a = inl a₁ ∧ b = inl b₁ ∧ inl c₁ = inl c₁_1 ∧ c₁_1 ∈ f a₁ b₁) …
  simp only [inl.injEq, exists_and_left, exists_eq_left']
  -- ⊢ ¬∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ inl c₁ = inr c₂ ∧ c₂ ∈ g a₂ b₂
  rintro ⟨_, _, c₂, _, _, h, _⟩
  -- ⊢ False
  exact inl_ne_inr h
  -- 🎉 no goals
#align finset.inl_mem_sum_lift₂ Finset.inl_mem_sumLift₂

theorem inr_mem_sumLift₂ {c₂ : γ₂} :
    inr c₂ ∈ sumLift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ := by
  rw [mem_sumLift₂, or_iff_right]
  -- ⊢ (∃ a₂ b₂ c₂_1, a = inr a₂ ∧ b = inr b₂ ∧ inr c₂ = inr c₂_1 ∧ c₂_1 ∈ g a₂ b₂) …
  simp only [inr.injEq, exists_and_left, exists_eq_left']
  -- ⊢ ¬∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ inr c₂ = inl c₁ ∧ c₁ ∈ f a₁ b₁
  rintro ⟨_, _, c₂, _, _, h, _⟩
  -- ⊢ False
  exact inr_ne_inl h
  -- 🎉 no goals
#align finset.inr_mem_sum_lift₂ Finset.inr_mem_sumLift₂

theorem sumLift₂_eq_empty :
    sumLift₂ f g a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧
        ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ := by
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  -- ⊢ (∀ (a₁ : α₁) (b₁ : β₁), a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧ ∀ (a₂ : α₂) …
  · constructor <;>
    -- ⊢ ∀ (a₁ : α₁) (b₁ : β₁), a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅
    · rintro a b rfl rfl
      -- ⊢ f a b = ∅
      -- ⊢ g a b = ∅
      -- 🎉 no goals
      exact map_eq_empty.1 h
      -- 🎉 no goals
  cases a <;> cases b
  -- ⊢ sumLift₂ f g (inl val✝) b = ∅
              -- ⊢ sumLift₂ f g (inl val✝¹) (inl val✝) = ∅
              -- ⊢ sumLift₂ f g (inr val✝¹) (inl val✝) = ∅
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)
    -- 🎉 no goals
#align finset.sum_lift₂_eq_empty Finset.sumLift₂_eq_empty

theorem sumLift₂_nonempty :
    (sumLift₂ f g a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨
        ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, not_imp]
  -- 🎉 no goals
#align finset.sum_lift₂_nonempty Finset.sumLift₂_nonempty

theorem sumLift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
    ∀ a b, sumLift₂ f₁ f₂ a b ⊆ sumLift₂ g₁ g₂ a b
  | inl _, inl _ => map_subset_map.2 (h₁ _ _)
  | inl _, inr _ => Subset.rfl
  | inr _, inl _ => Subset.rfl
  | inr _, inr _ => map_subset_map.2 (h₂ _ _)
#align finset.sum_lift₂_mono Finset.sumLift₂_mono

end SumLift₂

end Finset

open Finset Function

namespace Sum

variable {α β : Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

instance : LocallyFiniteOrder (Sum α β)
    where
  finsetIcc := sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by rintro (a | a) (b | b) (x | x) <;> simp
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
  finset_mem_Ico := by rintro (a | a) (b | b) (x | x) <;> simp
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
  finset_mem_Ioc := by rintro (a | a) (b | b) (x | x) <;> simp
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
  finset_mem_Ioo := by rintro (a | a) (b | b) (x | x) <;> simp
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals

variable (a₁ a₂ : α) (b₁ b₂ : β) (a b : Sum α β)

theorem Icc_inl_inl : Icc (inl a₁ : Sum α β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Icc_inl_inl Sum.Icc_inl_inl

theorem Ico_inl_inl : Ico (inl a₁ : Sum α β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ico_inl_inl Sum.Ico_inl_inl

theorem Ioc_inl_inl : Ioc (inl a₁ : Sum α β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ioc_inl_inl Sum.Ioc_inl_inl

theorem Ioo_inl_inl : Ioo (inl a₁ : Sum α β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl :=
  rfl
#align sum.Ioo_inl_inl Sum.Ioo_inl_inl

@[simp]
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Icc_inl_inr Sum.Icc_inl_inr

@[simp]
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Ico_inl_inr Sum.Ico_inl_inr

@[simp]
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl
#align sum.Ioc_inl_inr Sum.Ioc_inl_inr

@[simp, nolint simpNF] -- Porting note: dsimp can not prove this
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ := by
  rfl
  -- 🎉 no goals
#align sum.Ioo_inl_inr Sum.Ioo_inl_inr

@[simp]
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Icc_inr_inl Sum.Icc_inr_inl

@[simp]
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Ico_inr_inl Sum.Ico_inr_inl

@[simp]
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl
#align sum.Ioc_inr_inl Sum.Ioc_inr_inl

@[simp, nolint simpNF] -- Porting note: dsimp can not prove this
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ := by
  rfl
  -- 🎉 no goals
#align sum.Ioo_inr_inl Sum.Ioo_inr_inl

theorem Icc_inr_inr : Icc (inr b₁ : Sum α β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Icc_inr_inr Sum.Icc_inr_inr

theorem Ico_inr_inr : Ico (inr b₁ : Sum α β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ico_inr_inr Sum.Ico_inr_inr

theorem Ioc_inr_inr : Ioc (inr b₁ : Sum α β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ioc_inr_inr Sum.Ioc_inr_inr

theorem Ioo_inr_inr : Ioo (inr b₁ : Sum α β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr :=
  rfl
#align sum.Ioo_inr_inr Sum.Ioo_inr_inr

end Disjoint

end Sum
