/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Pointwise

#align_import combinatorics.additive.ruzsa_covering from "leanprover-community/mathlib"@"b363547b3113d350d053abdf2884e9850a56b205"

/-!
# Ruzsa's covering lemma

This file proves the Ruzsa covering lemma. This says that, for `s`, `t` finsets, we can cover `s`
with at most `(s + t).card / t.card` copies of `t - t`.

## TODO

Merge this file with other prerequisites to Freiman's theorem once we have them.
-/


open Pointwise

namespace Finset

variable {α : Type*} [DecidableEq α] [CommGroup α] (s : Finset α) {t : Finset α}

/-- **Ruzsa's covering lemma**. -/
@[to_additive "**Ruzsa's covering lemma**"]
theorem exists_subset_mul_div (ht : t.Nonempty) :
    ∃ u : Finset α, u.card * t.card ≤ (s * t).card ∧ s ⊆ u * t / t := by
  haveI : ∀ u, Decidable ((u : Set α).PairwiseDisjoint (· • t)) := fun u ↦ Classical.dec _
  set C := s.powerset.filter fun u ↦ u.toSet.PairwiseDisjoint (· • t)
  obtain ⟨u, hu, hCmax⟩ := C.exists_maximal (filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by rw [coe_empty]; exact Set.pairwiseDisjoint_empty⟩)
  rw [mem_filter, mem_powerset] at hu
  refine' ⟨u,
    (card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hu.2).ge.trans
      (card_le_of_subset <| mul_subset_mul_right hu.1),
    fun a ha ↦ _⟩
  rw [mul_div_assoc]
  by_cases hau : a ∈ u
  · exact subset_mul_left _ ht.one_mem_div hau
  by_cases H : ∀ b ∈ u, Disjoint (a • t) (b • t)
  · refine' (hCmax _ _ <| ssubset_insert hau).elim
    rw [mem_filter, mem_powerset, insert_subset_iff, coe_insert]
    exact ⟨⟨ha, hu.1⟩, hu.2.insert fun _ hb _ ↦ H _ hb⟩
  push_neg at H
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  refine' mem_mul.2 ⟨b, a / b, hb, _, by simp⟩
  exact mem_div.2 ⟨_, _, hc₂, hc₁, by simp [div_eq_mul_inv a b, mul_comm]⟩
#align finset.exists_subset_mul_div Finset.exists_subset_mul_div
#align finset.exists_subset_add_sub Finset.exists_subset_add_sub

end Finset
