/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Big operators on a finset in the natural numbers

This file contains the results concerning the interaction of finset big operators with natural
numbers.
-/

variable {ι : Type*}

namespace Finset

lemma even_sum_iff_even_card_odd {s : Finset ι} (f : ι → ℕ) :
    Even (∑ i ∈ s, f i) ↔ Even #{x ∈ s | Odd (f x)} := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x ↦ Even (f x)), Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, Nat.odd_iff.mp]
  simp_rw [← Finset.sum_filter, ← Nat.even_iff, Finset.card_eq_sum_ones]

lemma odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι → ℕ) :
    Odd (∑ i ∈ s, f i) ↔ Odd #{x ∈ s | Odd (f x)} := by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]

theorem card_preimage_eq_sum_card_image_eq {M : Type*} {f : ι → M} {s : Finset M}
    (hb : ∀ b ∈ s, Set.Finite {a | f a = b}) :
    Nat.card (f ⁻¹' s) = ∑ b ∈ s, Nat.card {a // f a = b} := by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b ∈ s, Nat.card {a //f a = b} = ∑ b ∈ t, Nat.card {a | f a = b} by
    exact (Finset.sum_subset (by simp [t]) (by aesop)).symm]
  have ht : Set.Finite (f ⁻¹' t) := Set.Finite.preimage' (finite_toSet t) (by aesop)
  rw [Nat.card_eq_card_finite_toFinset ht, Finset.card_eq_sum_card_image (f := f)]
  refine Finset.sum_congr ?_ fun m hm ↦ ?_
  · simpa [← Finset.coe_inj, t] using Set.image_preimage_eq_inter_range
  · rw [Nat.card_eq_card_finite_toFinset (hb _ (by aesop))]
    suffices {a | f a = m} ⊆ ht.toFinset from
      congr_arg (Finset.card ·) (Finset.ext_iff.mpr fun a ↦ by simpa using fun h ↦ this h)
    intro _ h
    simpa using by rwa [h]

end Finset
