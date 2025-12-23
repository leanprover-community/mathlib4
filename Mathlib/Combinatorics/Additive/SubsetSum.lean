/-
Copyright (c) 2025 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Powerset

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

public section

open scoped Pointwise

namespace Finset
variable {M : Type*} [DecidableEq M] [AddCommMonoid M] {A : Finset M} {a : M}

/-- The subset-sum of a finite set `A` in a commutative monoid is the set of all sums
of subsets of `A`. -/
def subsetSum (A : Finset M) : Finset M := A.powerset.image fun B ↦ B.sum id

lemma mem_subsetSum_iff : a ∈ A.subsetSum ↔ ∃ B ⊆ A, ∑ b ∈ B, b = a := by simp [subsetSum]

@[simp]
lemma zero_mem_subsetSum : 0 ∈ A.subsetSum := mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

@[simp] lemma subsetSum_nonempty : A.subsetSum.Nonempty := ⟨0, by simp⟩

lemma subset_subsetSum : A ⊆ A.subsetSum :=
  fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]
lemma subsetSum_mono {B : Finset M} (hAB : A ⊆ B) : A.subsetSum ⊆ B.subsetSum :=
  image_mono _ <| powerset_mono.mpr hAB

@[simp] lemma subsetSum_erase_zero : (A.erase 0).subsetSum = A.subsetSum := by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨B.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hB (mem_of_mem_erase hi)⟩

lemma vadd_finset_subsetSum_subset_subsetSum_insert (a_notin_A : a ∉ A) :
    a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum := by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact ⟨insert a B, by aesop, by rw [sum_insert (fun h => a_notin_A (hB h))]; simp⟩

variable [LinearOrder M] [IsOrderedCancelAddMonoid M]

lemma nonneg_of_mem_subsetSum (A_nonneg : ∀ x ∈ A, 0 ≤ x) : ∀ x ∈ A.subsetSum, 0 ≤ x := by
  simpa [mem_subsetSum_iff] using fun B hB ↦ Finset.sum_nonneg fun x hx ↦ A_nonneg _ <| hB hx

lemma card_add_card_subsetSum_lt_card_subsetSum_insert_max (hA : ∀ x ∈ A, 0 < x)
    (hAa : ∀ x ∈ A, x < a) (ha : 0 < a) :
    #A + #A.subsetSum < #(insert a A).subsetSum := by
  -- We show that `insert 0 A` and `a +ᵥ A.subsetSum` are disjoint subsets of
  -- `(insert a A).subsetSum`, and their combined cardinality gives the result.
  -- The sets are disjoint.
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    have := nonneg_of_mem_subsetSum (fun y hy ↦ (hA y hy).le)
    simpa [disjoint_left, mem_insert, mem_vadd_finset] using
      ⟨fun x hx => (add_pos_of_pos_of_nonneg ha <| this _ hx).ne',
        fun x hx y hy ↦ (lt_add_of_lt_of_nonneg (hAa x hx) <| this _ hy).ne'⟩
  -- Both sets are subsets of `(insert a A).subsetSum`.
  have insert_subset : insert 0 A ⊆ (insert a A).subsetSum := by
    grw [insert_subset_iff, ← subset_insert]; exact ⟨zero_mem_subsetSum, subset_subsetSum⟩
  have vadd_subset : a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (hAa a ha).false
  -- Count the sizes.
  calc #A + #A.subsetSum
    _ < #A + 1 + #A.subsetSum := by gcongr; exact Nat.lt_add_one _
    _ = #(insert 0 A) + #A.subsetSum := by rw [card_insert_of_notMem fun h => (hA 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by simp [vadd_finset_def, card_image_of_injOn]
    _ = #((insert 0 A) ∪ (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ ≤ #(insert a A).subsetSum := by grw [union_subset insert_subset vadd_subset]

-- The proof follows Theorem 3 in [Nathanson1995].
theorem card_succ_choose_two_lt_card_subsetSum_of_pos (A_pos : ∀ x ∈ A, 0 < x) :
    (#A + 1).choose 2 < #A.subsetSum := by
  induction A using induction_on_max with
  | h0 => simp
  | step a A A_lt_a ih =>
    have A_pos' : ∀ x ∈ A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    grw [card_insert_of_notMem fun ha => (A_lt_a a ha).false, Nat.choose_succ_left _ _ (by lia),
      Nat.choose_one_right, add_right_comm, add_assoc, Nat.add_one_le_iff.2 (ih A_pos')]
    exact card_add_card_subsetSum_lt_card_subsetSum_insert_max A_pos' A_lt_a <| A_pos a <|
      mem_insert_self a A

theorem card_choose_two_lt_card_subsetSum_of_nonneg (A_pos : ∀ x ∈ A, 0 ≤ x) :
    (#A).choose 2 < #A.subsetSum := by
  calc (#A).choose 2
    _ ≤ (#(A.erase 0) + 1).choose 2 := by grw [tsub_le_iff_right.1 <| pred_card_le_card_erase]
    _ < #(A.erase 0).subsetSum :=
        card_succ_choose_two_lt_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

end Finset
