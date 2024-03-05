/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.GRW.Core
import Mathlib.Init.Order.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Order.Bounds.Basic

/-! # Lemmas for the `grw` tactic

The `grw` tactic starts by trying all lemmas with the `@[grw]` annotation. The first (explicit)
argument should be related to the result type of the lemma via the rewrite. The other arguments
will be automatically solved using the `gcongr` tactic.

-/

namespace Mathlib.Tactic.GRW

@[grw] lemma rewrite_le {α : Type*} [Preorder α] {a b a' b' : α}
    (H : a ≤ b) (ha : a' ≤ a) (hb : b ≤ b') : a' ≤ b' := le_trans ha (le_trans H hb)

@[grw] lemma rewrite_lt {α : Type*} [Preorder α] {a b a' b' : α}
    (H : a < b) (ha : a' ≤ a) (hb : b ≤ b') : a' < b' := lt_of_le_of_lt ha (lt_of_lt_of_le H hb)

@[grw] lemma rewrite_mem {α : Type*} {a : α} {X X' : Set α}
    (H : a ∈ X) (hX : X ⊆ X') : a ∈ X' := hX H

@[grw] lemma rewrite_sub {α : Type*} {X Y X' Y' : Set α} (H : X ⊆ Y) (hX : X' ⊆ X) (hY : Y ⊆ Y') :
    X' ⊆ Y' := fun _ hx ↦ hY (H (hX hx))

@[grw] lemma rewrite_ssub {α : Type*} {X Y X' Y' : Set α} (H : X ⊂ Y) (hX : X' ⊆ X) (hY : Y ⊆ Y') :
    X' ⊂ Y' := lt_of_le_of_lt hX (lt_of_lt_of_le H hY)

@[grw] lemma rewrite_bddAbove {α : Type*} [Preorder α] {s s' : Set α}
    (H : BddAbove s) (hs : s' ⊆ s) : BddAbove s' := H.mono hs

@[grw] lemma rewrite_setNonempty {α : Type*} {s s' : Set α} (H : Set.Nonempty s) (hs : s ⊆ s') :
    Set.Nonempty s' := H.mono hs
