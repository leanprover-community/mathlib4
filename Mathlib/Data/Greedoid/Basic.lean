/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Greedoid.Accessible
import Mathlib.Data.Greedoid.Exchange

/-!
This file contains the definition of `ExchangeProperty` and `AccessibleProperty`, along with the
main subject `Greedoid α`.

# Greedoid
Greedoid is a set system, i.e., a family of sets, over a finite ground set, which satisfies both
exchange and accessible properties.
-/

/-- Greedoid is a nonempty (finite) set system satisfying both accessible and exchange property. -/
structure Greedoid (α : Type*) where
  /-- The ground set which every element lies on. -/
  ground_set : Finset α
  /-- The feasible set of the greedoid. -/
  feasible : Finset α → Prop
  contains_emptyset : feasible ∅
  exchange_property : Greedoid.ExchangeProperty feasible
  subset_ground : ∀ s, feasible s → s ⊆ ground_set

section Greedoid

variable {α : Type*}

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'· -/
protected def Greedoid.mem (G : Greedoid α) (s : Finset α) := G.feasible s

instance : Membership (Finset α) (Greedoid α) :=
  ⟨Greedoid.mem⟩

end Greedoid

namespace Greedoid

variable {α : Type*}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
    G₁.ground_set = G₂.ground_set → G₁.feasible = G₂.feasible → G₁ = G₂
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

@[simp]
theorem feasible_set_injective :
    Function.Injective (fun G : Greedoid α => (G.ground_set, G.feasible)) :=
  fun _ _ => by simp; exact eq_of_veq

@[simp]
theorem feasible_set_inj {G₁ G₂ : Greedoid α} :
    G₁.ground_set = G₂.ground_set ∧ G₁.feasible = G₂.feasible ↔ G₁ = G₂ :=
  ⟨fun h => by apply eq_of_veq <;> simp [h], fun h => by simp [h]⟩

variable {G : Greedoid α}
variable {s : Finset α}
variable {s₁ : Finset α} (hs₁ : s₁ ∈ G)
variable {s₂ : Finset α} (hs₂ : s₂ ∈ G)

protected theorem accessible_property :
    AccessibleProperty G.feasible := by
  intro s hs₁ hs₂
  by_contra h'; simp at h'
  let F : Set (Finset α) :=
    {t | G.feasible t ∧ t.card < s.card}
  have hF : ∅ ∈ F := by simp [F, G.contains_emptyset, hs₂]
  let F' : Finset α → Prop := fun t ↦
    t ∈ F ∧ ∀ t', G.feasible t' → t'.card < s.card → t'.card ≤ t.card
  have hF' : ∃ x, F' x := by
    by_contra h''; simp [F', F] at h''
    have h₁ : ∀ n, ∃ t, t ∈ F ∧ t.card = n := by
      intro n; induction n with
      | zero => use ∅; simp [hF]
      | succ n ih =>
        rcases ih with ⟨t, ht₁, ht₂⟩
        rcases ht₁ with ⟨ht₁, ht₃⟩
        rcases h'' t ht₁ ht₃ with ⟨u, hu₁, hu₂, hu₃⟩
        rcases G.exchange_property hu₁ ht₁ hu₃ with ⟨_, _, hx₁, hx₂⟩
        use t.cons _ hx₁
        simp [F, ht₂, hx₂]; omega
    rcases h₁ s.card with ⟨t, ht₁, ht₂⟩
    simp [F, ht₂] at ht₁
  rcases hF' with ⟨u, hu₁, hu₂⟩
  rcases hu₁ with ⟨_, hu₁⟩
  rcases ExchangeProperty.exists_superset_of_card_le
    G.exchange_property hs₁ G.contains_emptyset (le_of_lt hu₁) (zero_le _)
    with ⟨t, ht₁, _, ht₂, ht₃⟩
  simp at ht₂
  rw [← ht₃] at hu₁
  rcases G.exchange_property hs₁ ht₁ hu₁ with ⟨_, _, hx₁, hx₂⟩
  have h : (t.cons _ hx₁).card < s.card := by
    by_contra h''; simp at h''; apply h' _ ht₂ _ ht₁; omega
  have := card_cons _ ▸ ht₃ ▸ hu₂ _ hx₂ h; omega

instance : Accessible G.feasible :=
  ⟨G.accessible_property⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem : G.feasible s ↔ s ∈ G := by
  rfl

theorem mem_accessible
    (hs₁ : s ∈ G) (hs₂ : s.Nonempty) :
    ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ G :=
  G.accessible_property hs₁ hs₂

theorem mem_exchange
    (hs₁ : G.feasible s₁) (hs₂ : G.feasible s₂) (hs : s₂.card < s₁.card) :
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ G :=
  G.exchange_property hs₁ hs₂ hs

end Membership

@[simp]
theorem emptyset_feasible : ∅ ∈ G :=
  G.contains_emptyset

end Greedoid

