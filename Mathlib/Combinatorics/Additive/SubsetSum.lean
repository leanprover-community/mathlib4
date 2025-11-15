/-
Copyright (c) 2025 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

namespace Finset
variable {α : Type*} [DecidableEq α] [AddCommMonoid α] {A : Finset α}

/-- The subsetSum of a finite set `A` in a commutative monoid is the set of all sums
  of subsets of `A`. -/
def subsetSum (A : Finset α) : Finset α := A.powerset.image fun S ↦ S.sum id

theorem mem_subsetSum_iff {x : α} : x ∈ A.subsetSum ↔ ∃ a ⊆ A, a.sum id = x := by simp [subsetSum]

lemma subsetSum_zero_mem : 0 ∈ A.subsetSum :=
  mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

lemma subset_subsetSum : A ⊆ A.subsetSum :=
  fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

lemma subsetSum_mono {B : Finset α} (hAB : A ⊆ B) : A.subsetSum ⊆ B.subsetSum :=
  image_mono _ <| powerset_mono.mpr hAB

lemma subsetSum_eq_subsetSum_erase_zero : (A \ {0}).subsetSum = A.subsetSum := by
  refine le_antisymm (subsetSum_mono sdiff_subset) fun x hx => ?_
  obtain ⟨S, hS, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨S.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_sdiff.mpr ⟨hS (mem_of_mem_erase hi), by simp [mem_erase.mp hi]⟩

lemma subsetSum_image_add_notMem_subset_subsetSum_insert {a : α} (a_notin_A : a ∉ A) :
    A.subsetSum.image (· + a) ⊆ (insert a A).subsetSum := by
  simp_rw [subset_iff, mem_image, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨S, hS, rfl⟩, rfl⟩
  exact ⟨insert a S, by aesop, by rw [sum_insert (fun h => a_notin_A (hS h)), add_comm]; rfl⟩

variable {β : Type*} [AddCancelCommMonoid β] [LinearOrder β]
  [CanonicallyOrderedAdd β] {A : Finset β} {a : β}

lemma card_subsetSum_insert_max (A_lt_a : ∀ x ∈ A, x < a)
    (zero_notin_A : 0 ∉ A) (a_ne_zero : a ≠ 0) :
    A.card + 1 + A.subsetSum.card ≤ (insert a A).subsetSum.card := by
  -- We show that (insert 0 A) and A.subsetSum.image (· + a) are disjoint subsets
  -- of (insert a A).subsetSum, and their combined cardinality gives the result.
  have a_notin_A : a ∉ A := fun ha => (A_lt_a a ha).false

  -- The disjointness
  have zero_not_in_image : 0 ∉ A.subsetSum.image (· + a) := by simp [a_ne_zero]
  have disjoint : Disjoint (insert 0 A) (A.subsetSum.image (· + a)) := by
    rw [disjoint_insert_left, eq_true zero_not_in_image, true_and, disjoint_left]
    simp only [mem_image]
    rintro _ hxA ⟨b, _, rfl⟩
    exact (A_lt_a _ hxA).not_ge (le_add_of_nonneg_left (zero_le b))

  -- Both sets are subsets of (insert a A).subsetSum
  have insert_subset : insert 0 A ⊆ (insert a A).subsetSum :=
    insert_subset subsetSum_zero_mem
      (subset_subsetSum.trans (subsetSum_mono (subset_insert a A)))

  have image_subset : A.subsetSum.image (· + a) ⊆ (insert a A).subsetSum :=
    subsetSum_image_add_notMem_subset_subsetSum_insert a_notin_A

  -- Count the sizes
  calc A.card + 1 + A.subsetSum.card
    _ = (insert 0 A).card + A.subsetSum.card := by rw [card_insert_of_notMem zero_notin_A]
    _ = (insert 0 A).card + (A.subsetSum.image (· + a)).card := by
        simp only [card_image_of_injOn fun _ _ _ _ hxy => add_right_cancel hxy]
    _ = ((insert 0 A) ∪ A.subsetSum.image (· + a)).card := by rw [card_union_of_disjoint disjoint]
    _ ≤ (insert a A).subsetSum.card := card_le_card (union_subset insert_subset image_subset)

-- The proof follows Theorem 3 in [Nathanson1995].
theorem card_succ_choose_two_succ_le_card_subsetSum_of_zero_notMem (hA : 0 ∉ A) :
    (A.card + 1).choose 2 + 1 ≤ A.subsetSum.card := by
  induction A using induction_on_max with
  | h0 => rfl
  | step a A A_lt_a ih =>
    have zero_notin_A : 0 ∉ A := fun h => hA (by simp [h])
    have a_notin_A : a ∉ A := fun ha => (A_lt_a a ha).false
    rw [card_insert_of_notMem a_notin_A]
    calc ((A.card + 1) + 1).choose 2 + 1
      _ = (A.card + 1).choose 1 + (A.card + 1).choose 2 + 1 := by rw [Nat.choose_succ_left]; omega
      _ = A.card + 1 + (A.card + 1).choose 2 + 1 := by rw [Nat.choose_one_right]
      _ ≤ A.card + 1 + A.subsetSum.card := Nat.add_le_add_left (ih zero_notin_A) _
      _ ≤ (insert a A).subsetSum.card :=
          card_subsetSum_insert_max A_lt_a zero_notin_A fun ha ↦ hA (by simp [ha])

theorem card_choose_two_succ_le_card_subsetSum : A.card.choose 2 + 1 ≤ A.subsetSum.card := by
  have h := pred_card_le_card_erase (s := A) (a := 0)
  calc A.card.choose 2 + 1
    _ ≤ ((A.erase 0).card + 1).choose 2 + 1 := Nat.add_le_add_right (Nat.choose_mono 2 (by omega)) 1
    _ ≤ (A.erase 0).subsetSum.card :=
        card_succ_choose_two_succ_le_card_subsetSum_of_zero_notMem (by simp)
    _ = A.subsetSum.card := by rw [← sdiff_singleton_eq_erase, subsetSum_eq_subsetSum_erase_zero]

end Finset
