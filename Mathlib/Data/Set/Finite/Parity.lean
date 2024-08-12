/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite

/-!
# Finite sets and parity of their cardinality

This file contains lemmas concerning finite sets and parity of their cardinality.
-/

namespace Set.Finite

variable {V : Type _} {s : Set V}

lemma one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s)
    (he : Even (s.ncard)) : 1 < s.ncard := by
  have : s.ncard ≠ 0 := by
    intro h
    rw [@Set.nonempty_iff_ne_empty] at hn
    exact hn <| (Set.ncard_eq_zero hs).mp h
  have : s.ncard ≠ 1 := by
    intro h
    simp [h] at he
  omega

lemma even_card_diff_pair [DecidableEq V] {x y : V} {u : Set V} (hu : Set.Finite u)
    (he : Even u.ncard) (hx : x ∈ u) (hy : y ∈ u) (hxy : x ≠ y) :
    Even ((u \ {x, y} : Set V).ncard) := by
  haveI : Fintype u := hu.fintype
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_diff, Finset.card_sdiff (by
    simp only [Set.toFinset_insert, Set.toFinset_singleton, Set.subset_toFinset, Finset.coe_insert,
      Finset.coe_singleton, Set.pair_subset hx hy]
    )]
  simp only [Set.toFinset_card, Set.toFinset_insert, Set.toFinset_singleton,
    Finset.mem_singleton, hxy, not_false_eq_true, Finset.card_insert_of_not_mem,
    Finset.card_singleton, Nat.reduceAdd]
  rw [Nat.even_sub (by
    simpa [← Set.Nat.card_coe_set_eq, ← Fintype.card_eq_nat_card] using
      Set.Finite.one_lt_ncard_of_nonempty_of_even hu (Set.nonempty_of_mem hx) he)]
  simp only [even_two, iff_true]
  rwa [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]

end Set.Finite
