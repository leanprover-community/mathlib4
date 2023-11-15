/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Tactic.GRW.Core

/-! # Lemmas for the `grw` tactic

The `grw` tactic starts by trying all lemmas with the `@[grw]` annotation. The first (explicit)
argument should be related to the result type of the lemma via the rewrite. The other arguments
will be automatically solved using the `gcongr` tactic.

The `@[grw_weaken]` annotation is used to automically replace rules of the form `a < b`
with `a ≤ b`.

-/

namespace Mathlib.Tactic.GRW

@[grw]
lemma rewrite_le {α : Type} [Preorder α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ a) (h₃ : b ≤ d) :
    c ≤ d := le_trans h₂ (le_trans h₁ h₃)

@[grw]
lemma rewrite_lt {α : Type} [Preorder α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ a) (h₃ : b ≤ d) :
    c < d := lt_of_le_of_lt h₂ (lt_of_lt_of_le h₁ h₃)

@[grw]
lemma rewrite_mem {α : Type} {a : α} {X Y: Set α} (h₁ : a ∈ X) (h₂ : X ⊆ Y) : a ∈ Y := h₂ h₁

@[grw]
lemma rewrite_sub {α : Type} {X Y Z W: Set α} (h₁ : X ⊆ Y) (h₂ : Z ⊆ X) (h₃ : Y ⊆ W) :
    (Z ⊆ W) := fun _ hx ↦ h₃ (h₁ (h₂ hx))

@[grw]
lemma rewrite_ssub {α : Type} {X Y Z W: Set α} (h₁ : X ⊂ Y) (h₂ : Z ⊆ X) (h₃ : Y ⊆ W) :
    (Z ⊂ W) := lt_of_le_of_lt h₂ (lt_of_lt_of_le h₁ h₃)

@[grw_weaken]
lemma weaken_lt {α : Type} [Preorder α] {a b : α} (h₁ : a < b) : a ≤ b := le_of_lt h₁
