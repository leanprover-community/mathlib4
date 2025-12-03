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

variable {β : Type*} [AddCommMonoid β] [LinearOrder β]
  [IsOrderedCancelAddMonoid β] {A : Finset β} {a : β}

lemma subsetSum_nonneg_of_nonneg (A_nonneg : ∀ x ∈ A, 0 ≤ x) : ∀ x ∈ A.subsetSum, 0 ≤ x := by
  intro _ hx
  obtain ⟨S, hS, rfl⟩ := mem_subsetSum_iff.mp hx
  exact sum_induction _ (0 ≤ ·) (fun _ _ => add_nonneg) (le_refl 0) fun a ha => A_nonneg a (hS ha)

lemma subsetSum_nonneg_of_pos (A_pos : ∀ x ∈ A, 0 < x) : ∀ x ∈ A.subsetSum, 0 ≤ x :=
  subsetSum_nonneg_of_nonneg fun x hx => (A_pos x hx).le

lemma card_subsetSum_of_pos_insert_max (A_pos : ∀ x ∈ A, 0 < x) (A_lt_a : ∀ x ∈ A, x < a)
    (zero_ls_a : 0 < a) :
    A.card + 1 + A.subsetSum.card ≤ (insert a A).subsetSum.card := by
  -- We show that (insert 0 A) and A.subsetSum.image (· + a) are disjoint subsets
  -- of (insert a A).subsetSum, and their combined cardinality gives the result.

  -- The disjointness
  have disjoint : Disjoint (insert 0 A) (A.subsetSum.image (· + a)) := by
    refine disjoint_insert_left.mpr ⟨?_, disjoint_left.mpr fun x hxA hy => ?_⟩
    · simp
      exact fun b hb => (add_pos_of_nonneg_of_pos (subsetSum_nonneg_of_pos A_pos b hb)
        zero_ls_a).ne'
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
      exact (A_lt_a (b + a) hxA).not_ge (le_add_of_nonneg_left (subsetSum_nonneg_of_pos A_pos b hb))

  -- Both sets are subsets of (insert a A).subsetSum
  have insert_subset : insert 0 A ⊆ (insert a A).subsetSum :=
    insert_subset subsetSum_zero_mem
      (subset_subsetSum.trans (subsetSum_mono (subset_insert a A)))

  have image_subset : A.subsetSum.image (· + a) ⊆ (insert a A).subsetSum :=
    subsetSum_image_add_notMem_subset_subsetSum_insert fun ha => (A_lt_a a ha).false

  -- Count the sizes
  calc A.card + 1 + A.subsetSum.card
    _ = (insert 0 A).card + A.subsetSum.card := by
        rw [card_insert_of_notMem fun h => (A_pos 0 h).false]
    _ = (insert 0 A).card + (A.subsetSum.image (· + a)).card := by
        simp only [card_image_of_injOn fun _ _ _ _ hxy => add_right_cancel hxy]
    _ = ((insert 0 A) ∪ A.subsetSum.image (· + a)).card := by rw [card_union_of_disjoint disjoint]
    _ ≤ (insert a A).subsetSum.card := card_le_card (union_subset insert_subset image_subset)

-- The proof follows Theorem 3 in [Nathanson1995].
theorem card_succ_choose_two_succ_le_card_subsetSum_of_pos (A_pos : ∀ x ∈ A, 0 < x) :
    (A.card + 1).choose 2 + 1 ≤ A.subsetSum.card := by
  induction A using induction_on_max with
  | h0 => rfl
  | step a A A_lt_a ih =>
    have A_pos' : ∀ x ∈ A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    rw [card_insert_of_notMem fun ha => (A_lt_a a ha).false]
    calc ((A.card + 1) + 1).choose 2 + 1
      _ = (A.card + 1).choose 1 + (A.card + 1).choose 2 + 1 := by rw [Nat.choose_succ_left]; omega
      _ = A.card + 1 + (A.card + 1).choose 2 + 1 := by rw [Nat.choose_one_right]
      _ ≤ A.card + 1 + A.subsetSum.card := Nat.add_le_add_left (ih A_pos') _
      _ ≤ (insert a A).subsetSum.card :=
          card_subsetSum_of_pos_insert_max A_pos' A_lt_a (A_pos a (mem_insert_self a A))

theorem card_choose_two_succ_le_card_subsetSum_of_nonneg (A_pos : ∀ x ∈ A, 0 ≤ x) :
    A.card.choose 2 + 1 ≤ A.subsetSum.card := by
  have _ := pred_card_le_card_erase (s := A) (a := 0)
  calc A.card.choose 2 + 1
    _ ≤ ((A.erase 0).card + 1).choose 2 + 1 := Nat.add_le_add_right (Nat.choose_mono 2 (by omega)) 1
    _ ≤ (A.erase 0).subsetSum.card :=
        card_succ_choose_two_succ_le_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = A.subsetSum.card := by rw [← sdiff_singleton_eq_erase, subsetSum_eq_subsetSum_erase_zero]

end Finset
