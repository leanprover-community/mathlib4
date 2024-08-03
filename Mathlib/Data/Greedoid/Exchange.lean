import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic

namespace Greedoid

open Nat Finset

variable {α : Type*}

/-- The exchange property of greedoid.
    Note that the exchange property also hold for (finite) matroids. -/
def ExchangeProperty (Sys : Finset α → Prop) :=
  ⦃s₁ : Finset α⦄ → Sys s₁ →
  ⦃s₂ : Finset α⦄ → Sys s₂ →
  s₂.card < s₁.card →
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, Sys (cons x s₂ h)

/-- A set system satisfies the exchange property if there is some element `x` in some feasible
    `s₁`, which is not in `s₂` with smaller cardinaliy, and `s₂ ∪ {x}` is also feasible.
    This implies that all maximal feasible sets are actually maximum. -/
class Exchange (Sys : Finset α → Prop) : Prop :=
  exchange:
    ⦃s₁ : Finset α⦄ → Sys s₁ →
    ⦃s₂ : Finset α⦄ → Sys s₂ →
    s₂.card < s₁.card →
      ∃ x ∈ s₁, ∃ h : x ∉ s₂, Sys (cons x s₂ h)

namespace Exchange

open Nat Finset

variable {Sys : Finset α → Prop} [Exchange Sys]
variable {s₁ : Finset α} (hs₁ : Sys s₁)
variable {s₂ : Finset α} (hs₂ : Sys s₂)

-- TODO: Find a better name.
theorem exchange_exists_superset_of_card_le
    {n : ℕ} (hn₁ : n ≤ s₁.card) (hn₂ : s₂.card ≤ n) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ (∀ e ∈ s, e ∈ s₁ ∨ e ∈ s₂) ∧ s.card = n := by
    induction n, hn₂ using le_induction with
    | base => use s₂; simp [hs₂]; intro _ h; exact .inr h
    | succ _ h ih =>
      rcases ih (by omega) with ⟨s, hs, h₁, h₂, rfl⟩
      rcases Exchange.exchange hs₁ hs hn₁ with ⟨a, ha₁, ha₂, ha₃⟩
      use cons a s ha₂; simp_all
      intro _ h; simp [h₁ h] 

-- TODO: Find a better name.
theorem exchange_exists_feasible_superset_add_element_feasible'
    (hs : s₂ ⊆ s₁)
    {n : ℕ} (hn : n = s₁.card - s₂.card)
    {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ s ⊆ s₁ ∧ ∃ h : a ∉ s, Sys (cons a s h) := by
  induction n generalizing s₂ with
  | zero => exact False.elim ((eq_of_subset_of_card_le hs (Nat.le_of_sub_eq_zero hn.symm) ▸ ha₂) ha₁)
  | succ n ih =>
    rcases exchange_exists_superset_of_card_le hs₁ hs₂ (by omega) (le_succ _)
      with ⟨s, hs₁, hs₂, hs₃, hs₄⟩
    by_cases h : a ∈ s
    · 
      sorry
    · sorry

theorem exchange_exists_feasible_superset_add_element_feasible := sorry



end Exchange

end Greedoid
