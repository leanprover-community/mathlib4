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

The `grw` tactic starts by trying lemmas with the `@[grw]` annotation, looking for one whose "key"
(which should be a predicate) matches the form of the hypothesis or goal being rewritten at. The
key of a `@[grw]` lemma is the head symbol of the result type of the lemma, and this must also be
the same as the head symbol of the last argument of the lemma.

At the time of tagging a lemma with the `@[grw]` attribute, it is recorded which other arguments of
the lemma are of the form `x ∼ y` for some relation `∼` and some free variables `x`, `y` appearing
in matching positions in the result and last argument to the lemma (in either order).  These
arguments are referred to as "main" arguments to the lemma.  When the lemma is used for generalized
rewriting, the `gcongr` tactic will be used to find proofs for these arguments.

-/

namespace Mathlib.Tactic.GRW

@[grw] lemma rewrite_le {α : Type*} [Preorder α] {a b a' b' : α}
    (ha : a' ≤ a) (hb : b ≤ b') (H : a ≤ b) : a' ≤ b' := le_trans ha (le_trans H hb)

@[grw] lemma rewrite_lt {α : Type*} [Preorder α] {a b a' b' : α}
    (ha : a' ≤ a) (hb : b ≤ b') (H : a < b) : a' < b' := lt_of_le_of_lt ha (lt_of_lt_of_le H hb)

@[grw] lemma rewrite_mem {α : Type*} {a : α} {X X' : Set α}
    (hX : X ⊆ X') (H : a ∈ X) : a ∈ X' := hX H

@[grw] lemma rewrite_sub {α : Type*} {X Y X' Y' : Set α} (hX : X' ⊆ X) (hY : Y ⊆ Y') (H : X ⊆ Y) :
    X' ⊆ Y' := fun _ hx ↦ hY (H (hX hx))

@[grw] lemma rewrite_ssub {α : Type*} {X Y X' Y' : Set α} (hX : X' ⊆ X) (hY : Y ⊆ Y') (H : X ⊂ Y) :
    X' ⊂ Y' := lt_of_le_of_lt hX (lt_of_lt_of_le H hY)

@[grw] lemma rewrite_bddAbove {α : Type*} [Preorder α] {s s' : Set α}
    (hs : s' ⊆ s) (H : BddAbove s) : BddAbove s' := H.imp fun _ hc _ hx => hc (hs hx)

@[grw] lemma rewrite_setNonempty {α : Type*} {s s' : Set α} (hs : s ⊆ s') (H : Set.Nonempty s) :
    Set.Nonempty s' := H.mono hs
