/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finite.Defs

/-!
# Definition and basic properties of `ℕ∞`-valued cardinality
-/

open Classical

namespace ENat

/-- Cardinality of a type, as a `ℕ∞`. Returns `⊤` for all infinite types. -/
noncomputable def card (α : Sort*) : ℕ∞ :=
  if _ : Finite α then (Finite.exists_equiv_fin α).choose else ⊤

notation "#ₑ" => ENat.card

@[simp] theorem card_eq_top_iff {α : Sort*} : #ₑ α = ⊤ ↔ Infinite α := by simp [card]
@[simp] theorem card_infinite (α : Type*) [Infinite α] : #ₑ α = ⊤ := by simpa

end ENat
