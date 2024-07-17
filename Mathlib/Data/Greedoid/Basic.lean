/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
This file contains the definition of `ExchangeProperty` and `AccessibleProperty`, along with the
main subject `Greedoid α`.

# Greedoid
Greedoid is a set system, i.e., a family of sets, over a finite ground set, which satisfies both
exchange and accessible properties.

## Exchange Property and Accessible Property of Greedoid
If a set system `S` satisfies the exchange property, then there is some element `x ∈ s₂ \ s₁`
which `s₁ ∪ {x} ∈ S`, for every set `s₁, s₂ ∈ S` satisfying `s₁.card < s₂.card`.
If a set system `S` satisfies the accessible property, then there is some element `x ∈ s`
which `s \ {x} ∈ S` for every nonempty set `s ∈ S`.
These two properties are defined in this file as `ExchangeProperty` and `AccessibleProperty`.
-/

namespace Greedoid

open Nat Finset

/-- The exchange property of greedoid.
    Note that the exchange property also hold for (finite) matroids. -/
def ExchangeProperty {α : Type*} (Sys : Finset (Finset α)) :=
  ⦃s₁ : Finset α⦄ → s₁ ∈ Sys →
  ⦃s₂ : Finset α⦄ → s₂ ∈ Sys →
  s₂.card < s₁.card →
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ Sys

instance {α : Type*} [DecidableEq α] :
    @DecidablePred (Finset (Finset α)) ExchangeProperty :=
  fun Sys => by unfold ExchangeProperty; infer_instance

/-- The accessible property of greedoid -/
def AccessibleProperty {α : Type*} (Sys : Finset (Finset α)) : Prop :=
  ⦃s : Finset α⦄ → s ∈ Sys → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ Sys

/-- A set system is accessible if there is some element `x` in `s` which `s \ {x}` is also in the
    set system, for each nonempty set `s` of the set system.
    This automatically implies that nonempty accessible set systems contain an empty set. -/
class Accessible {α : Type*} (Sys : Finset (Finset α)) : Prop where
  accessible : ⦃s : Finset α⦄ → s ∈ Sys → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ Sys

end Greedoid

/-- Greedoid is a nonempty (finite) set system satisfying both accessible and exchange property. -/
structure Greedoid (α : Type*) where
  /-- The ground set which every element lies on. -/
  ground_set : Finset α
  /-- The feasible set of the greedoid. -/
  feasible_set : Finset (Finset α)
  contains_emptyset : ∅ ∈ feasible_set
  accessible_property : Greedoid.AccessibleProperty feasible_set
  exchange_property : Greedoid.ExchangeProperty feasible_set
  subset_ground : ∀ s ∈ feasible_set, s ⊆ ground_set

section Greedoid

variable {α : Type*}

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'· -/
protected def Greedoid.mem (s : Finset α) (G : Greedoid α) := s ∈ G.feasible_set

instance : Membership (Finset α) (Greedoid α) :=
  ⟨Greedoid.mem⟩

instance [DecidableEq α] {G : Greedoid α} : DecidablePred (fun s => s ∈ G) := fun s =>
  if h : s ∈ G.feasible_set
    then isTrue h
    else isFalse fun h' => h h'

end Greedoid

namespace Greedoid

variable {α : Type*}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
    G₁.ground_set = G₂.ground_set → G₁.feasible_set = G₂.feasible_set → G₁ = G₂
  | ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

@[simp]
theorem feasible_set_injective :
    Function.Injective (fun G : Greedoid α => (G.ground_set, G.feasible_set)) :=
  fun _ _ => by simp; exact eq_of_veq

@[simp]
theorem feasible_set_inj {G₁ G₂ : Greedoid α} :
    G₁.ground_set = G₂.ground_set ∧ G₁.feasible_set = G₂.feasible_set ↔ G₁ = G₂ :=
  ⟨fun h => by apply eq_of_veq <;> simp [h], fun h => by simp [h]⟩

instance [DecidableEq α] : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h₁ : G₁.ground_set = G₂.ground_set
    then if h₂ : G₁.feasible_set = G₂.feasible_set
      then isTrue (eq_of_veq h₁ h₂)
      else isFalse (fun h' => h₂ (h' ▸ rfl))
    else isFalse (fun h' => h₁ (h' ▸ rfl))

variable {G : Greedoid α}

variable {s : Finset α}
variable {s₁ : Finset α} (hs₁ : s₁ ∈ G)
variable {s₂ : Finset α} (hs₂ : s₂ ∈ G)

instance : Accessible G.feasible_set := ⟨G.accessible_property⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem : s ∈ G.feasible_set ↔ s ∈ G := by rfl

theorem mem_accessible (hs₁ : s ∈ G.feasible_set) (hs₂ : s.Nonempty) :
    ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ G :=
  G.accessible_property hs₁ hs₂

theorem mem_exchange (hs : s₂.card < s₁.card) :
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ G :=
  G.exchange_property hs₁ hs₂ hs

end Membership

@[simp]
theorem greedoid_nonempty : G.feasible_set.Nonempty := ⟨∅, G.contains_emptyset⟩

end Greedoid
