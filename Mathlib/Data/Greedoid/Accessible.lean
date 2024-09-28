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

-- TODO: Add doc.
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

-- TODO: Add doc.
theorem induction_on_accessible'
    (hS : Sys ∅)
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

theorem induction_on_accessible
    (hS : Sys ∅)
    {p : ⦃s : Finset α⦄ → Sys s → Prop}
    (empty : p hS)
    (insert :
      ∀ ⦃s₁ : Finset α⦄, (hs₁ : Sys s₁) →
      ∀ ⦃s₂ : Finset α⦄, (hs₂ : Sys s₂) →
      s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p hs₂ → p hs₁) :
    ∀ {s : Finset α} (hs : Sys s), p hs
  | _, h => induction_on_accessible' hS empty insert h rfl

end Accessible

end Greedoid

