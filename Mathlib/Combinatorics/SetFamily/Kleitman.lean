/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Combinatorics.SetFamily.Intersecting

#align_import combinatorics.set_family.kleitman from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Kleitman's bound on the size of intersecting families

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `Finset.card_biUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

open Fintype (card)

variable {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Kleitman's theorem**. An intersecting family on `n` elements contains at most `2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no previous family. -/
theorem Finset.card_biUnion_le_of_intersecting (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.biUnion f).card ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - s.card) := by
  have : DecidableEq ι := by
    classical
    infer_instance
  obtain hs | hs := le_total (Fintype.card α) s.card
  -- ⊢ card (Finset.biUnion s f) ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - card s)
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    -- ⊢ card (Finset.biUnion s f) ≤ 2 ^ Fintype.card α - 1
    refine' (card_le_of_subset <| biUnion_subset.2 fun i hi a ha ↦
      mem_compl.2 <| not_mem_singleton.2 <| (hf _ hi).ne_bot ha).trans_eq _
    rw [card_compl, Fintype.card_finset, card_singleton]
    -- 🎉 no goals
  induction' s using Finset.cons_induction with i s hi ih generalizing f
  -- ⊢ card (Finset.biUnion ∅ f) ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - card ∅)
  · simp
    -- 🎉 no goals
  set f' : ι → Finset (Finset α) :=
    fun j ↦ if hj : j ∈ cons i s hi then (hf j hj).exists_card_eq.choose else ∅
  have hf₁ : ∀ j, j ∈ cons i s hi → f j ⊆ f' j ∧ 2 * (f' j).card =
      2 ^ Fintype.card α ∧ (f' j : Set (Finset α)).Intersecting := by
    rintro j hj
    simp_rw [dif_pos hj, ← Fintype.card_finset]
    exact Classical.choose_spec (hf j hj).exists_card_eq
  have hf₂ : ∀ j, j ∈ cons i s hi → IsUpperSet (f' j : Set (Finset α)) := by
    refine' fun j hj ↦ (hf₁ _ hj).2.2.isUpperSet' ((hf₁ _ hj).2.2.is_max_iff_card_eq.2 _)
    rw [Fintype.card_finset]
    exact (hf₁ _ hj).2.1
  refine' (card_le_of_subset <| biUnion_mono fun j hj ↦ (hf₁ _ hj).1).trans _
  -- ⊢ card (Finset.biUnion (cons i s hi) fun j => f' j) ≤ 2 ^ Fintype.card α - 2 ^ …
  nth_rw 1 [cons_eq_insert i]
  -- ⊢ card (Finset.biUnion (insert i s) fun j => f' j) ≤ 2 ^ Fintype.card α - 2 ^  …
  rw [biUnion_insert]
  -- ⊢ card (f' i ∪ Finset.biUnion s fun j => f' j) ≤ 2 ^ Fintype.card α - 2 ^ (Fin …
  refine' (card_mono <| @le_sup_sdiff _ _ _ <| f' i).trans ((card_union_le _ _).trans _)
  -- ⊢ card (f' i) + card ((f' i ∪ Finset.biUnion s fun j => f' j) \ f' i) ≤ 2 ^ Fi …
  rw [union_sdiff_left, sdiff_eq_inter_compl]
  -- ⊢ card (f' i) + card ((Finset.biUnion s fun j => f' j) ∩ (f' i)ᶜ) ≤ 2 ^ Fintyp …
  refine' le_of_mul_le_mul_left _ (pow_pos (zero_lt_two' ℕ) <| Fintype.card α + 1)
  -- ⊢ 2 ^ (Fintype.card α + 1) * (card (f' i) + card ((Finset.biUnion s fun j => f …
  rw [pow_succ', mul_add, mul_assoc, mul_comm _ 2, mul_assoc]
  -- ⊢ 2 ^ Fintype.card α * (2 * card (f' i)) + 2 * (2 ^ Fintype.card α * card ((Fi …
  refine' (add_le_add
      ((mul_le_mul_left <| pow_pos (zero_lt_two' ℕ) _).2
      (hf₁ _ <| mem_cons_self _ _).2.2.card_le) <|
      (mul_le_mul_left <| zero_lt_two' ℕ).2 <| IsUpperSet.card_inter_le_finset _ _).trans _
  · rw [coe_biUnion]
    -- ⊢ IsUpperSet (⋃ (x : ι) (_ : x ∈ ↑s), ↑(f' x))
    exact isUpperSet_iUnion₂ fun i hi ↦ hf₂ _ <| subset_cons _ hi
    -- 🎉 no goals
  · rw [coe_compl]
    -- ⊢ IsLowerSet (↑(f' i))ᶜ
    exact (hf₂ _ <| mem_cons_self _ _).compl
    -- 🎉 no goals
  rw [mul_tsub, card_compl, Fintype.card_finset, mul_left_comm, mul_tsub,
    (hf₁ _ <| mem_cons_self _ _).2.1, two_mul, add_tsub_cancel_left, ← mul_tsub, ← mul_two,
    mul_assoc, ← add_mul, mul_comm]
  refine' mul_le_mul_left' _ _
  -- ⊢ 2 ^ Fintype.card α + card (Finset.biUnion s fun j => f' j) ≤ 2 * (2 ^ Fintyp …
  refine' (add_le_add_left
    (ih _ (fun i hi ↦ (hf₁ _ <| subset_cons _ hi).2.2)
    ((card_le_of_subset <| subset_cons _).trans hs)) _).trans _
  rw [mul_tsub, two_mul, ← pow_succ,
    ← add_tsub_assoc_of_le (pow_le_pow' (one_le_two : (1 : ℕ) ≤ 2) tsub_le_self),
    tsub_add_eq_add_tsub hs, card_cons, add_tsub_add_eq_tsub_right]
#align finset.card_bUnion_le_of_intersecting Finset.card_biUnion_le_of_intersecting
