/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Card

/-!
# Exchange property

This file contains the definition of `ExchangeProperty`,
along with some main properties of set systems with the exchange property.
Not to be confused with 'Exchange System'. [Brylawski & Dieter, 1986]

A set system `S` satisfies the exchange property if there is some `x ∈ s \ t` for `s, t ∈ S`
which `#t < #s`, that `t ∪ {x} ∈ S`.
This definition is modified in the implementation to remove the need of decidability:
-/

namespace Greedoid

open Nat Finset

variable {α : Type*}

-- TODO: Is typeclass `Exchange` required?
/-- The exchange property of greedoid.
    Note that the exchange property also hold for (finite) matroids.

    A set system satisfies the exchange property if there is some element `x` in some feasible
    `s₁`, which is not in `s₂` with smaller cardinaliy, and `s₂ ∪ {x}` is also feasible.
    This implies that all maximal feasible sets are actually maximum. -/
def ExchangeProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s₁ : Finset α⦄ → Sys s₁ →
  ⦃s₂ : Finset α⦄ → Sys s₂ →
  #s₂ < #s₁ →
  ∃ x ∈ s₁, ∃ h : x ∉ s₂, Sys (cons x s₂ h)

namespace ExchangeProperty

open Nat Finset

variable {Sys : Finset α → Prop}
variable {s₁ : Finset α} {s₂ : Finset α}

-- TODO: Find a better name.
theorem exists_superset_of_card_le
    (hS : ExchangeProperty Sys) (hs₁ : Sys s₁) (hs₂ : Sys s₂)
    {n : ℕ} (hn₁ : n ≤ #s₁) (hn₂ : #s₂ ≤ n) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ (∀ e ∈ s, e ∈ s₁ ∨ e ∈ s₂) ∧ #s = n := by
    induction n, hn₂ using le_induction
    case base => use s₂; simp only [hs₂, subset_refl, true_and]; exact ⟨fun _ h ↦ .inr h, ⟨⟩⟩
    case succ _ h ih =>
      rcases ih (by omega) with ⟨s, hs, h₁, h₂, rfl⟩
      rcases hS hs₁ hs hn₁ with ⟨a, ha₁, ha₂, ha₃⟩
      use cons a s ha₂; refine ⟨ha₃, subset_trans h₁ (subset_cons _), fun _ h₃ ↦ ?_, card_cons ha₂⟩
      exact (mem_cons.mp h₃).elim (fun h ↦ .inl (h ▸ ha₁)) fun h ↦ h₂ _ h

-- TODO: Find a better name.
theorem exists_feasible_superset_add_element_feasible
    (hS : ExchangeProperty Sys) (hs₁ : Sys s₁) (hs₂ : Sys s₂) (hs : s₂ ⊆ s₁)
    {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ s ⊆ s₁ ∧ ∃ h : a ∉ s, Sys (cons a s h) := by
  induction' hn : #s₁ - #s₂ generalizing s₂
  case zero => exact False.elim ((eq_of_subset_of_card_le hs (Nat.le_of_sub_eq_zero hn) ▸ ha₂) ha₁)
  case succ _ ih =>
    rcases exists_superset_of_card_le hS hs₁ hs₂ (by omega) (le_succ _)
      with ⟨s, hs₃, hs₄, hs₅, hs₆⟩
    by_cases h : a ∈ s
    · use s₂, hs₂, subset_rfl, hs, ha₂
      exact (eq_of_subset_of_card_le
        ((@cons_subset _ _ _ _ ha₂).mpr ⟨h, hs₄⟩)  (hs₆ ▸ card_cons ha₂ ▸ le_rfl)) ▸ hs₃
    · rcases ih hs₃ (fun e h ↦ (hs₅ _ h).elim id (fun f ↦ hs f)) h (by omega)
        with ⟨t, ht₁, ht₂, ht₃⟩
      use t, ht₁, subset_trans hs₄ ht₂

end ExchangeProperty

end Greedoid

