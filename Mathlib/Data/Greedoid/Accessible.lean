import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic

namespace Greedoid

open Nat Finset

variable {α : Type*}

def AccessibleProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

class Accessible (Sys : Finset α → Prop) : Prop where
  accessible :
    ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

namespace Accessible

variable {Sys : Finset α → Prop} [Accessible Sys]

/-- A helper lemma for `nonempty_contains_emptyset`.-/
theorem nonempty_contains_emptyset'
    {s : Finset α} (hs : Sys s) {n : ℕ} (hn : n = s.card) :
    Sys ∅ := by
  induction n generalizing s with
  | zero => exact card_eq_zero.mp hn.symm ▸ hs
  | succ _ ih =>
    rcases Accessible.accessible hs (by rw[← card_ne_zero]; omega) with ⟨t, _, _, ht⟩
    exact ih ht (by omega)

theorem nonempty_contains_emptyset
    (h : ∃ s, Sys s) :
    Sys ∅ :=
  have ⟨_, h⟩ := h; nonempty_contains_emptyset' h rfl

@[simp]
theorem nonempty_contains_emptyset_iff :
    (∃ s, Sys s) ↔ Sys ∅ :=
  ⟨fun h => nonempty_contains_emptyset h, fun h => ⟨∅, h⟩⟩

section Induction

variable (hS : Sys ∅)

-- TODO: Find better name.
/-- A helper lemma for `induction_on_accessible`.-/
theorem induction_on_accessible'
    {p : ⦃s : Finset α⦄ → Sys s → Prop}
    (empty : p hS)
    (insert :
      ∀ ⦃s₁ : Finset α⦄, (hs₁ : Sys s₁) →
      ∀ ⦃s₂ : Finset α⦄, (hs₂ : Sys s₂) →
      s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p hs₂ → p hs₁)
    {s : Finset α} (hs : Sys s) {n : ℕ} (hn : n = s.card) :
    p hs := by
  induction n generalizing s with
  | zero => exact card_eq_zero.mp hn.symm ▸ empty
  | succ n ih =>
    rcases Accessible.accessible hs (one_le_card.mp (by omega)) with ⟨t, ht₁, ht₂, ht₃⟩
    exact insert hs ht₃ ht₁ ht₂ (ih ht₃ (by omega))

-- TODO: Find better name.
theorem induction_on_accessible
    {p : ⦃s : Finset α⦄ → Sys s → Prop}
    (empty : p hS)
    (insert :
      ∀ ⦃s₁ : Finset α⦄, (hs₁ : Sys s₁) →
      ∀ ⦃s₂ : Finset α⦄, (hs₂ : Sys s₂) →
      s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p hs₂ → p hs₁) :
    ∀ {s : Finset α} (hs : Sys s), p hs
  | _, h => induction_on_accessible' hS empty insert h rfl

end Induction

-- TODO: Find better name.
theorem construction_on_accessible
    [DecidableEq α] {s : Finset α} (hs : Sys s) :
    ∃ l : List α, l.Nodup ∧ Multiset.ofList l = s.val ∧ ∀ l', l' <:+ l →
      ∃ s', Multiset.ofList l' = s'.val ∧ Sys s' := by
  have hS := nonempty_contains_emptyset ⟨s, hs⟩
  induction hs using induction_on_accessible hS with
  | empty => use []; simp; use ∅; simp [hS]
  | insert hs₁ hs₂ h₁ h₂ h₃ =>
    rename_i s₁ s₂
    rcases h₃ with ⟨l₀, hl₀₁, hl₀₂, hl₀₃⟩
    have h₄ : ∃! a, a ∈ s ∧ a ∉ l₀ := by sorry
    let x : α := s.choose (· ∉ l₀) h₄
    have hx : x ∉ l₀ := choose_property _ _ h₄
    use x :: l₀
    apply And.intro (by simp [hl₀₁, hx])
    apply And.intro (Multiset.eq_of_le_of_card_le _ _)
    · intro l' hl'
      rw [List.suffix_cons_iff] at hl'
      apply hl'.elim _ (fun h => hl₀₃ _ h)
      intro hl'; use s₁; simp [hs₁, hl']
      apply Multiset.eq_of_le_of_card_le
      · sorry
      · simp [← h₂]
        sorry
    · sorry
    · simp [← h₂]
      sorry

end Accessible

end Greedoid

