/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Card

#align_import algebra.order.field.pi from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `Algebra.Order.Field.Basic` to avoid importing the finiteness hierarchy there.
-/


variable {α ι : Type*} [LinearOrderedSemifield α]

theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i := by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  exact
    ⟨_, half_pos hε, fun i =>
      add_lt_add_left ((half_lt_self hε).trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
#align pi.exists_forall_pos_add_lt Pi.exists_forall_pos_add_lt
