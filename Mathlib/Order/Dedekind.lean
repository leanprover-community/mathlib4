/-
Copyright (c) 2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson, Violeta Hernández Palacios
-/
import Mathlib.Order.CompleteLattice.Defs

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

We provide an explicit construction, as the set of "lower cuts" of the order, meaning sets with
`lowerBounds (upperBounds s) = s`. The dual construction as upper cuts, or sets with
`upperBounds (lowerBounds s) = s` would also work; keeping this in mind, we keep the API symmetric.
-/

open Set

variable {α : Type*} {s t : Set α} [Preorder α]

/-! ### Lower cuts and upper cuts -/

/-- The set of lower cuts in a preorder is the set of sets with
`lowerBounds (upperBounds s) ⊆ s`.

The theorem `mem_lowerCuts_iff_eq` shows the equivalence to the condition
`lowerBounds (upperBounds s) = s` -/
def lowerCuts (α : Type*) [Preorder α] : Set (Set α) :=
  {s | lowerBounds (upperBounds s) ⊆ s}

theorem mem_lowerCuts_iff_eq : s ∈ lowerCuts α ↔ lowerBounds (upperBounds s) = s := by
  rw [lowerCuts, subset_antisymm_iff]
  simp [subset_lowerBounds_upperBounds]

theorem inter_mem_lowerCuts (hs : s ∈ lowerCuts α) (ht : t ∈ lowerCuts α) : s ∩ t ∈ lowerCuts α :=
  fun _ ha ↦ ⟨hs fun _ hb ↦ ha fun _ ⟨hc, _⟩ ↦ hb hc, ht fun _ hb ↦ ha fun _ ⟨_, hc⟩ ↦ hb hc⟩

theorem sInter_mem_lowerCuts {S : Set (Set α)} (hS : S ⊆ lowerCuts α) : ⋂₀ S ∈ lowerCuts α := by
  intro a ha t ht
  rw [← mem_lowerCuts_iff_eq.mp (hS ht)]
  exact fun _ hb ↦ ha fun _ hc ↦ hb (hc _ ht)

theorem sInter_lowerCuts_mem_lowerCuts : ⋂₀ lowerCuts α ∈ lowerCuts α :=
  sInter_mem_lowerCuts (le_refl _)

theorem Iic_mem_lowerCuts (a : α) : Iic a ∈ lowerCuts α := fun _ hb ↦ hb fun _ ↦ id

/-- The set of lower cuts in a preorder is the set of sets with
`upperBounds (lowerBounds s) ⊆ s`.

The theorem `mem_upperCuts_iff_eq` shows the equivalence to the condition
`upperBounds (lowerBounds s) = s` -/
def upperCuts (α : Type*) [Preorder α] : Set (Set α) :=
  {s | upperBounds (lowerBounds s) ⊆ s}

theorem mem_upperCuts_iff_eq : s ∈ upperCuts α ↔ upperBounds (lowerBounds s) = s :=
  mem_lowerCuts_iff_eq (α := αᵒᵈ)

theorem inter_mem_upperCuts (hs : s ∈ upperCuts α) (ht : t ∈ upperCuts α) :
    s ∩ t ∈ upperCuts α :=
  inter_mem_lowerCuts (α := αᵒᵈ) hs ht

theorem sInter_mem_upperCuts {S : Set (Set α)} (hS : S ⊆ upperCuts α) : ⋂₀ S ∈ upperCuts α :=
  sInter_mem_lowerCuts (α := αᵒᵈ) hS

theorem sInter_upperCuts_mem_upperCuts : ⋂₀ upperCuts α ∈ upperCuts α :=
  sInter_mem_upperCuts (le_refl _)

theorem Ici_mem_lowerCuts (a : α) : Iic a ∈ lowerCuts α := fun _ hb ↦ hb fun _ ↦ id

theorem upperBounds_mem_upperCuts_of_mem_lowerCuts (H : s ∈ lowerCuts α) :
    upperBounds s ∈ upperCuts α := by
  simp_all [mem_upperCuts_iff_eq, mem_lowerCuts_iff_eq]

theorem lowerBounds_mem_lowerCuts_of_mem_upperCuts (H : s ∈ upperCuts α) :
    lowerBounds s ∈ lowerCuts α := by
  simp_all [mem_upperCuts_iff_eq, mem_lowerCuts_iff_eq]
