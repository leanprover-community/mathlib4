/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finite.Defs

/-!
# Definition of `ℕ∞`-valued cardinality
-/

open Classical

namespace ENat

/-- Cardinality of a type, as a `ℕ∞`. Returns `⊤` for all infinite types. -/
noncomputable def card (α : Sort*) : ℕ∞ :=
  if _ : Finite α then (Finite.exists_equiv_fin α).choose else ⊤

notation "#ₑ" => ENat.card

lemma card_eq_top_iff {α : Sort*} : #ₑ α = ⊤ ↔ Infinite α := by simp [card]
@[simp] lemma card_infinite (α : Type*) [Infinite α] : #ₑ α = ⊤ := by rwa [card_eq_top_iff]

lemma card_lt_top_iff {α : Sort*} : #ₑ α < ⊤ ↔ Finite α := by
  simp [lt_top_iff_ne_top, card_eq_top_iff.not]

@[simp] lemma card_lt_top (α : Sort*) [Finite α] : #ₑ α < ⊤ := card_lt_top_iff.2 ‹_›
@[simp] lemma card_ne_top (α : Sort*) [Finite α] : #ₑ α ≠ ⊤ := (card_lt_top α).ne

end ENat
