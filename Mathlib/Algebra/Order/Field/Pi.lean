/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Notation.Pi
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `Algebra.Order.Field.Basic` to avoid importing the finiteness hierarchy there.
-/

variable {α ι : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α]
  [Nontrivial α] [DenselyOrdered α]

theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i := by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · obtain ⟨a, ha⟩ := exists_ne (0 : α)
    obtain ha | ha := ha.lt_or_gt <;> obtain ⟨b, hb, -⟩ := exists_pos_add_of_lt' ha <;>
      exact ⟨b, hb, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  exact ⟨δ, hδ, fun i ↦ add_lt_add_left (hδε.trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
