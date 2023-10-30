import Mathlib.Tactic.GRW.Core

open Mathlib.Tactic.GRW

@[grw]
theorem rewrite_le {α : Type} [Preorder α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ a) (h₃ : b ≤ d)
    : c ≤ d := le_trans h₂ (le_trans h₁ h₃)

@[grw]
theorem rewrite_lt {α : Type} [Preorder α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ a) (h₃ : b ≤ d)
    : c < d := lt_of_le_of_lt h₂ (lt_of_lt_of_le h₁ h₃)

@[grw]
theorem rewrite_mem {α : Type} {a : α} {X Y: Set α} (h₁ : a ∈ X) (h₂ : X ⊆ Y) : a ∈ Y := h₂ h₁

@[grw]
theorem rewrite_sub {α : Type} {X Y Z W: Set α} (h₁ : X ⊆ Y) (h₂ : Z ⊆ X) (h₃ : Y ⊆ W)
    : (Z ⊆ W) := fun _ hx ↦ h₃ (h₁ (h₂ hx))

@[grw]
theorem rewrite_ssub {α : Type} {X Y Z W: Set α} (h₁ : X ⊂ Y) (h₂ : Z ⊆ X) (h₃ : Y ⊆ W)
    : (Z ⊂ W) := lt_of_le_of_lt h₂ (lt_of_lt_of_le h₁ h₃)

@[grw_weaken]
theorem weaken_lt {α : Type} [Preorder α] {a b : α} (h₁ : a < b) : a ≤ b := le_of_lt h₁
