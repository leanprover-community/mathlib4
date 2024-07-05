/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Card.Defs

open Function
open scoped Classical

namespace ENat

section sort

variable {α β : Sort*}

theorem card_congr (e : α ≃ β) : #ₑ α = #ₑ β := by
  have : ∀ {n}, Nonempty (α ≃ Fin n) ↔ Nonempty (β ≃ Fin n) :=
    ⟨Nonempty.map e.symm.trans, Nonempty.map e.trans⟩
  simp only [card, e.finite_iff, this]

@[simp]
theorem card_fin (n : ℕ) : #ₑ (Fin n) = n := by
  simp [card, finite_iff_exists_equiv_fin, Fin.equiv_iff_eq]

end sort

end ENat
