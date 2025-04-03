/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Cast.Basic

/-!
# Cardinality of a finite set and subtraction

This file contains results on the cardinality of a `Finset` and subtraction, by casting the
cardinality as element of an `AddGroupWithOne`.

## Main results

* `Finset.cast_card_erase_of_mem`: erasing an element of a finset decrements the cardinality
  (avoiding `ℕ` subtraction).
* `Finset.cast_card_inter`, `Finset.cast_card_union`: inclusion/exclusion principle.
* `Finset.cast_card_sdiff`: cardinality of `t \ s` is the difference of cardinalities if `s ⊆ t`.
-/

assert_not_exists MonoidWithZero OrderedCommMonoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b : α}

section InsertErase

variable [DecidableEq α]
/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$.
  This result is casted to any additive group with 1,
  so that we don't have to work with `ℕ`-subtraction. -/
@[simp]
theorem cast_card_erase_of_mem {R} [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
    (#(s.erase a) : R) = #s - 1 := by
  rw [card_erase_of_mem hs, Nat.cast_sub, Nat.cast_one]
  rw [Nat.add_one_le_iff, Finset.card_pos]
  exact ⟨a, hs⟩

end InsertErase

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α]

lemma cast_card_inter [AddGroupWithOne R] :
    (#(s ∩ t) : R) = #s + #t - #(s ∪ t) := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_inter_add_card_union, cast_add]

lemma cast_card_union [AddGroupWithOne R] :
    (#(s ∪ t) : R) = #s + #t - #(s ∩ t) := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_union_add_card_inter, cast_add]

lemma cast_card_sdiff [AddGroupWithOne R] (h : s ⊆ t) : (#(t \ s) : R) = #t - #s := by
  rw [card_sdiff h, Nat.cast_sub (card_mono h)]

end Lattice

end Finset
