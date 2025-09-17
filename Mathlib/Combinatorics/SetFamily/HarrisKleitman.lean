/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.UpperLower.Basic

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `#𝒜 * #ℬ` and
`2 ^ card α * #(𝒜 ∩ ℬ)` where `𝒜` and `ℬ` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `IsLowerSet.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

theorem IsLowerSet.nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.nonMemberSubfamily a : Set (Finset α)) := fun s t hts => by
  simp_rw [mem_coe, mem_nonMemberSubfamily]
  exact And.imp (h hts) (mt <| @hts _)

theorem IsLowerSet.memberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.memberSubfamily a : Set (Finset α)) := by
  rintro s t hts
  simp_rw [mem_coe, mem_memberSubfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

theorem IsLowerSet.memberSubfamily_subset_nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    𝒜.memberSubfamily a ⊆ 𝒜.nonMemberSubfamily a := fun s => by
  rw [mem_memberSubfamily, mem_nonMemberSubfamily]
  exact And.imp_left (h <| subset_insert _ _)

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset' (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) (h𝒜s : ∀ t ∈ 𝒜, t ⊆ s) (hℬs : ∀ t ∈ ℬ, t ⊆ s) :
    #𝒜 * #ℬ ≤ 2 ^ #s * #(𝒜 ∩ ℬ) := by
  induction s using Finset.induction generalizing 𝒜 ℬ with
  | empty =>
    simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [card_empty, zero_mul, empty_inter, mul_zero, le_refl]
    obtain rfl | rfl := hℬs
    · simp only [card_empty, inter_empty, mul_zero, le_refl]
    · simp only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton,
        le_refl]
  | insert a s hs ih =>
  rw [card_insert_of_notMem hs, ← card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜, ←
    card_memberSubfamily_add_card_nonMemberSubfamily a ℬ, add_mul, mul_add, mul_add,
    add_comm (_ * _), add_add_add_comm]
  refine
    (add_le_add_right
          (mul_add_mul_le_mul_add_mul
              (card_le_card h𝒜.memberSubfamily_subset_nonMemberSubfamily) <|
            card_le_card hℬ.memberSubfamily_subset_nonMemberSubfamily)
          _).trans
      ?_
  rw [← two_mul, pow_succ', mul_assoc]
  have h₀ : ∀ 𝒞 : Finset (Finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) →
      ∀ t ∈ 𝒞.nonMemberSubfamily a, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_nonMemberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : ∀ 𝒞 : Finset (Finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) →
      ∀ t ∈ 𝒞.memberSubfamily a, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_memberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  refine mul_le_mul_left' ?_ _
  refine (add_le_add (ih h𝒜.memberSubfamily hℬ.memberSubfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
    ih h𝒜.nonMemberSubfamily hℬ.nonMemberSubfamily (h₀ _ h𝒜s) <| h₀ _ hℬs).trans_eq ?_
  rw [← mul_add, ← memberSubfamily_inter, ← nonMemberSubfamily_inter,
    card_memberSubfamily_add_card_nonMemberSubfamily]

variable [Fintype α]

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
h𝒜.le_card_inter_finset' hℬ (fun _ _ => subset_univ _) fun _ _ => subset_univ _

/-- **Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrelate. -/
theorem IsUpperSet.card_inter_le_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ := by
  rw [← isLowerSet_compl, ← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this

/-- **Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrelate. -/
theorem IsLowerSet.card_inter_le_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ := by
  rw [inter_comm, mul_comm #𝒜]
  exact hℬ.card_inter_le_finset h𝒜

/-- **Harris-Kleitman inequality**: Any two upper sets of finsets correlate. -/
theorem IsUpperSet.le_card_inter_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) := by
  rw [← isLowerSet_compl, ← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this
  · exact mul_le_mul_left' (card_le_card inter_subset_right) _
  · rw [← Fintype.card_finset]
    exact mul_le_mul_right' (card_le_univ _) _
