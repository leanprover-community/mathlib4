/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity

/-!
# Big operators on a finset in the natural numbers

This file contains the results concerning the interaction of finset big operators with natural
numbers.
-/

variable {ι : Type*}

namespace Finset


lemma even_sum_of_even_card_odd {s : Finset ι} (f : ι → ℕ)
    (h : Even ((Finset.subtype (fun x ↦ Odd (f x)) s).card)) : Even (∑ i ∈ s, f i) := by
  simp only [Finset.card_subtype, Nat.odd_iff_not_even] at h
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x ↦ Even (f x))]
  rw [Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [@Finset.card_eq_sum_ones] at h
  rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_filter]
  have (a : ι): (if ¬Even (f a) then f a % 2 else 0) = if ¬Even (f a) then 1 else 0 := by
    split_ifs
    · rfl
    · rwa [← @Nat.odd_iff, @Nat.odd_iff_not_even]
  simp only [this, ← Finset.sum_filter, ← Nat.even_iff]
  exact h

end Finset
