/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Greedoid.Accessible
import Mathlib.Data.Greedoid.Exchange
-- import Mathlib.Order.Defs.PartialOrder

/-!
# Greedoid

This file contains the definition of `ExchangeProperty` and `AccessibleProperty`, along with the
main subject `Greedoid α`.

Greedoid is a set system, i.e., a family of sets, over a finite ground set, which satisfies both
exchange and accessible properties.
-/

/-- Greedoid is a nonempty (finite) set system satisfying both accessible and exchange property. -/
structure Greedoid (α : Type*) where
  /-- The ground set which every element lies on. -/
  ground : Finset α
  /-- The feasible property of the greedoid. -/
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  exchange_property : Greedoid.ExchangeProperty Feasible
  subset_ground : ∀ s, Feasible s → s ⊆ ground

section Greedoid

variable {α : Type*}

end Greedoid

namespace Greedoid

variable {α : Type*}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
    G₁.ground = G₂.ground → G₁.Feasible = G₂.Feasible → G₁ = G₂
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

@[simp]
theorem feasible_injective :
    Function.Injective (fun G : Greedoid α => (G.ground, G.Feasible)) :=
  fun _ _ => by simp; exact eq_of_veq

@[simp]
theorem feasible_inj {G₁ G₂ : Greedoid α} :
    G₁.ground = G₂.ground ∧ G₁.Feasible = G₂.Feasible ↔ G₁ = G₂ :=
  ⟨fun h => by apply eq_of_veq <;> simp [h], fun h => by simp [h]⟩

variable {G : Greedoid α}
variable {s : Finset α}
variable {s₁ : Finset α} (hs₁ : G.Feasible s₁)
variable {s₂ : Finset α} (hs₂ : G.Feasible s₂)

protected theorem accessible_property :
    AccessibleProperty G.Feasible := by
  intro s h₁ h₂; by_contra h'; simp only [not_exists, not_and] at h'
  have ⟨u, hu₁, hu₂⟩ : ∃ t : Finset α, #t < #s ∧ ∀ t', G.Feasible t' → #t' < #s → #t' ≤ #t := by
    by_contra h''; simp only [not_exists, not_and, not_forall, not_le] at h''
    have h₁ : ∀ n, ∃ t, G.Feasible t ∧ #t < #s ∧ #t = n := by
      intro n; induction n with
      | zero => exact ⟨∅, G.feasible_empty, card_pos.mpr h₂, rfl⟩
      | succ n ih =>
        rcases ih with ⟨t, ht₁, ht₂, _⟩
        rcases h'' t ht₂ with ⟨_, hu₁, _, hu₂⟩
        rcases G.exchange_property hu₁ ht₁ hu₂ with ⟨_, _, h₁, h₂⟩
        exact ⟨t.cons _ h₁, h₂, card_cons _ ▸ by omega, card_cons _ ▸ by omega⟩
    rcases h₁ #s with ⟨_, _, _⟩; omega
  rcases ExchangeProperty.exists_superset_of_card_le
    G.exchange_property h₁ G.feasible_empty (le_of_lt hu₁) (zero_le _)
    with ⟨t, ht₁, _, ht₂, ht₃⟩
  simp only [not_mem_empty, or_false] at ht₂; rw [← ht₃] at hu₁
  rcases G.exchange_property h₁ ht₁ hu₁ with ⟨_, _, hx₁, hx₂⟩
  have h : #(t.cons _ hx₁) < #s := by by_contra h''; simp at h''; apply h' _ ht₂ _ ht₁; omega
  have := card_cons _ ▸ ht₃ ▸ hu₂ _ hx₂ h; omega

instance : Accessible G.Feasible :=
  ⟨G.accessible_property⟩

end Greedoid

